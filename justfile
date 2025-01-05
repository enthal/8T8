set shell := ["/usr/bin/env", "bash"]

default: count-pld

count-pld:
    #!/usr/bin/env bash
    find . -type f -iname '*.pld' | while read -r file; do
        dir=$(dirname "$file")
        if [ ! -f "$dir/.skipmake" ]; then
            echo "Processing $file:"
            wc "$file"
        else
            echo "Skipping $file (because $dir/.skipmake exists)"
        fi
    done
