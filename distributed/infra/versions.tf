# The fleet for the harness's SSH backend: instances in up to three regions, plus a cluster placement group in the
# first region for the same-zone throughput case. Written to be read and applied by the operator only; the harness
# never creates cloud resources. `terraform apply` writes `hosts.toml`, the fleet file `vinc-distributed` reads.
terraform {
  required_version = ">= 1.6"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.80"
    }
    local = {
      source  = "hashicorp/local"
      version = "~> 2.5"
    }
  }
}
