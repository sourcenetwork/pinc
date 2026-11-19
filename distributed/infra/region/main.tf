# The machines of one region: a small VPC of their own, Elastic IPs allocated before anything that names them, a
# security group that admits SSH from the operator and everything from the other machines of the fleet, and the
# instances (the first `hosts` spread normally, then `cluster_hosts` in one cluster placement group).
terraform {
  required_providers {
    aws = { source = "hashicorp/aws" }
  }
}

variable "name" { type = string }
variable "hosts" { type = number }
variable "cluster_hosts" { type = number }
variable "instance_type" { type = string }
variable "ssh_public_key" { type = string }
variable "operator_cidr" { type = string }
variable "peer_cidrs" { type = list(string) }

data "aws_availability_zones" "up" {
  state = "available"
}

data "aws_ssm_parameter" "al2023" {
  name = "/aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-x86_64"
}

locals {
  count = var.hosts + var.cluster_hosts
  az    = data.aws_availability_zones.up.names[0]
  tags  = { Name = var.name, purpose = "pinc-distributed" }
}

resource "aws_vpc" "this" {
  cidr_block           = "10.200.0.0/16"
  enable_dns_hostnames = true
  tags                 = local.tags
}

resource "aws_internet_gateway" "this" {
  vpc_id = aws_vpc.this.id
  tags   = local.tags
}

resource "aws_subnet" "this" {
  vpc_id            = aws_vpc.this.id
  cidr_block        = "10.200.1.0/24"
  availability_zone = local.az
  tags              = local.tags
}

resource "aws_route_table" "this" {
  vpc_id = aws_vpc.this.id
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.this.id
  }
  tags = local.tags
}

resource "aws_route_table_association" "this" {
  subnet_id      = aws_subnet.this.id
  route_table_id = aws_route_table.this.id
}

resource "aws_eip" "host" {
  count  = local.count
  domain = "vpc"
  tags   = merge(local.tags, { Name = "${var.name}-${count.index}" })
}

resource "aws_security_group" "this" {
  name        = var.name
  description = "pinc-distributed: SSH from the operator, everything between the fleet's machines"
  vpc_id      = aws_vpc.this.id
  ingress {
    description = "SSH from the operator"
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = [var.operator_cidr]
  }
  ingress {
    description = "every protocol between the fleet's machines"
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = var.peer_cidrs
  }
  ingress {
    description = "every protocol inside the region's network"
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = [aws_vpc.this.cidr_block]
  }
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  tags = local.tags
}

resource "aws_key_pair" "this" {
  key_name   = var.name
  public_key = var.ssh_public_key
  tags       = local.tags
}

resource "aws_placement_group" "cluster" {
  count    = var.cluster_hosts > 0 ? 1 : 0
  name     = "${var.name}-cluster"
  strategy = "cluster"
  tags     = local.tags
}

resource "aws_instance" "host" {
  count                  = local.count
  ami                    = data.aws_ssm_parameter.al2023.value
  instance_type          = var.instance_type
  subnet_id              = aws_subnet.this.id
  vpc_security_group_ids = [aws_security_group.this.id]
  key_name               = aws_key_pair.this.key_name
  placement_group        = count.index >= var.hosts ? aws_placement_group.cluster[0].id : null
  root_block_device {
    volume_size = 20
    volume_type = "gp3"
  }
  # tc and the netem module, for the scenarios that add loss or delay on top of the real path.
  user_data = <<-EOT
    #!/bin/bash
    dnf install -y iproute-tc kernel-modules-extra
    modprobe sch_netem || true
  EOT
  tags = merge(local.tags, { Name = "${var.name}-${count.index}", cluster = count.index >= var.hosts ? "yes" : "no" })
}

resource "aws_eip_association" "host" {
  count         = local.count
  instance_id   = aws_instance.host[count.index].id
  allocation_id = aws_eip.host[count.index].id
}

output "addresses" {
  value = aws_eip.host[*].public_ip
}

output "hosts" {
  value = [for i in range(local.count) : {
    name       = "${var.name}-${i}"
    public_ip  = aws_eip.host[i].public_ip
    private_ip = aws_instance.host[i].private_ip
    cluster    = i >= var.hosts
  }]
}
