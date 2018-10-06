#!/usr/bin/env ruby

require 'fileutils'
require 'open3'


stack_haddock_stderr = Open3.capture3('stack haddock')[1]


# Example: ".stack-work/install/x86_64-osx/lts-10.2/8.2.2/doc"
built_docs_dir = stack_haddock_stderr.lines.select do |x|
  x.match(/\.stack-work/)
end.map do |x|
  x.chomp.sub(/^.*\.stack-work/, './.stack-work')
end.select do |x|
  x.match(/\/doc\//)
end.map do |x|
  x.sub(/\/doc\/.*$/,'/doc')
end.first


puts stack_haddock_stderr


# Copy built docs to 
if built_docs_dir && Dir.exist?(built_docs_dir)
  puts "Built_docs_dir: #{built_docs_dir}"

  unless File.exist?('.gitignore')
    puts "No .gitignore in current directory, assuming you're not running this right and exiting"
    exit
  end

  if Dir.exist?('doc/')
    puts "Removing previous doc/ dir"
    FileUtils.rm_rf 'doc/'
  else
    puts "No previous doc/ dir to remove"
  end

  FileUtils.cp_r built_docs_dir, 'doc/'
  puts "Docs copied to doc/"
else
  puts "Unable to find 'built_docs_dir', docs not copied to doc/"
end

