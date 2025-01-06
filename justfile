set shell := ["/usr/bin/env", "bash"]

default: pld

pld:
    #!/usr/bin/env bash
    find pld -type f -iname '*.pld' | while read -r pld; do
        dir=$(dirname "$pld")
        if [ ! -f "$dir/.nobuild" ]; then
            jed=$(echo $pld | sed "s:\\.pld\$:.jed:ig")
            # ls -l $pld $jed
            # [ -f "$jed" ] && echo "exists"
            # [ ! -f "$jed" ] && echo "not exists"
            # [ "$pld" -nt "$jed" ] && echo newer
            if [ ! -f "$jed" ] || [ "$pld" -nt "$jed" ]; then
                echo
                echo "🤖 CUPL build: $pld ..."
                just pld-file "$pld"
            fi
        fi
    done

pld-file FILE:
    #!/usr/bin/env bash
    set -ex

    dir=$(mktemp -d ~/.wine/drive_c/temp/build-XXXXXX)
    cp "{{FILE}}" "${dir}/"

    # See: http://bitsavers.informatik.uni-stuttgart.de/test_equipment/logicalDevices/CUPL_2.0_card.pdf
    WINEPATH="C:\Wincupl\WinCupl\Fitters" \
    wine \
        "C:\Wincupl\shared\cupl.exe" \
            -m3lxfjnabe \
            -u "C:\Wincupl\shared/Atmel.dl" \
            "c:\/temp/$(basename $dir)/$(basename "{{FILE}}")"

    cp ${dir}/*.jed ${dir}/*.doc $(dirname "{{FILE}}")/
