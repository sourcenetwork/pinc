# One provider per region (Terraform needs a static alias for each; unused ones create nothing).
provider "aws" {
  alias  = "r0"
  region = var.regions[0]
}

provider "aws" {
  alias  = "r1"
  region = length(var.regions) > 1 ? var.regions[1] : var.regions[0]
}

provider "aws" {
  alias  = "r2"
  region = length(var.regions) > 2 ? var.regions[2] : var.regions[0]
}

locals {
  regions = length(var.regions)
}

module "r0" {
  source            = "./region"
  providers         = { aws = aws.r0 }
  name              = "${var.name}-${var.regions[0]}"
  hosts             = var.hosts_per_region
  cluster_hosts     = var.cluster_hosts
  instance_type     = var.instance_type
  ssh_public_key    = var.ssh_public_key
  operator_cidr     = var.operator_cidr
  peer_cidrs        = local.peer_cidrs
}

module "r1" {
  count          = local.regions > 1 ? 1 : 0
  source         = "./region"
  providers      = { aws = aws.r1 }
  name           = "${var.name}-${var.regions[1]}"
  hosts          = var.hosts_per_region
  cluster_hosts  = 0
  instance_type  = var.instance_type
  ssh_public_key = var.ssh_public_key
  operator_cidr  = var.operator_cidr
  peer_cidrs     = local.peer_cidrs
}

module "r2" {
  count          = local.regions > 2 ? 1 : 0
  source         = "./region"
  providers      = { aws = aws.r2 }
  name           = "${var.name}-${var.regions[2]}"
  hosts          = var.hosts_per_region
  cluster_hosts  = 0
  instance_type  = var.instance_type
  ssh_public_key = var.ssh_public_key
  operator_cidr  = var.operator_cidr
  peer_cidrs     = local.peer_cidrs
}

# Every machine reaches every other one over the internet on its Elastic IP; the security groups admit exactly those
# addresses, so the elastic addresses are allocated first and the rules name them.
locals {
  addresses  = concat(module.r0.addresses, flatten(module.r1[*].addresses), flatten(module.r2[*].addresses))
  peer_cidrs = [for a in local.addresses : "${a}/32"]
  sites = concat(
    [for h in module.r0.hosts : merge(h, { site = var.regions[0] })],
    flatten([for m in module.r1 : [for h in m.hosts : merge(h, { site = var.regions[1] })]]),
    flatten([for m in module.r2 : [for h in m.hosts : merge(h, { site = var.regions[2] })]]),
  )
}

resource "local_file" "hosts" {
  filename        = "${path.module}/hosts.toml"
  file_permission = "0644"
  content         = templatefile("${path.module}/hosts.toml.tftpl", { hosts = local.sites })
}
