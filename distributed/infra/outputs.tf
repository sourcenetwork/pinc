output "hosts_file" {
  description = "The fleet file to pass to `vinc-distributed run --hosts`."
  value       = local_file.hosts.filename
}

output "addresses" {
  description = "Every machine's public address."
  value       = local.addresses
}
