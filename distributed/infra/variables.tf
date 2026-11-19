variable "regions" {
  description = "Up to three regions, one site each (the first also holds the cluster placement group)."
  type        = list(string)
  default     = ["us-east-2", "us-west-2", "eu-central-1"]
  validation {
    condition     = length(var.regions) >= 1 && length(var.regions) <= 3
    error_message = "Name one to three regions."
  }
}

variable "hosts_per_region" {
  description = "Machines per region; each runs one node or a few."
  type        = number
  default     = 2
}

variable "cluster_hosts" {
  description = "Machines in the cluster placement group of the first region, for the same-zone throughput case (0 for none)."
  type        = number
  default     = 2
}

variable "instance_type" {
  description = <<-EOT
    The instance type of every machine. Types rated "up to" a bandwidth (most of 4xlarge and below) run on burst credits
    for minutes and then drop to their baseline, which skews long measurements: prefer a type with a fixed rate (8xlarge
    and above), or keep runs short and say so. One flow (one QUIC connection) is capped at 5 Gbit/s outside a cluster
    placement group and 10 Gbit/s inside one.
  EOT
  type        = string
  default     = "c6in.8xlarge"
}

variable "ssh_public_key" {
  description = "The public key the harness logs in with (the content of a .pub file)."
  type        = string
}

variable "operator_cidr" {
  description = "Where SSH is allowed from (the operator's address as a /32)."
  type        = string
}

variable "name" {
  description = "A prefix for every resource, so a fleet is easy to find and remove."
  type        = string
  default     = "pinc-distributed"
}
