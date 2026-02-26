#!/bin/bash
# Count axioms and sorries in pphi2 and gaussian-field
# Usage: ./scripts/count_axioms.sh

PPHI2_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GF_DIR="$PPHI2_DIR/../gaussian-field"

RED='\033[0;31m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

echo "========================================"
echo "  Axiom & Sorry Counter"
echo "  $(date '+%Y-%m-%d %H:%M')"
echo "========================================"

count_file() {
    local file="$1"
    local pattern="$2"
    local n
    # Skip lines marked with count_axioms:skip (e.g. axioms inside comments)
    n=$(grep "$pattern" "$file" 2>/dev/null | grep -cv 'count_axioms:skip') || true
    n=$(echo "$n" | tr -cd '0-9')
    echo "${n:-0}"
}

count_in_dir() {
    local dir="$1"
    local label="$2"
    shift 2
    local src_dirs=("$@")

    echo ""
    echo -e "${CYAN}=== $label ===${NC}"
    echo ""

    local total_axioms=0
    local total_sorries=0

    printf "%-50s %8s %8s\n" "File" "Axioms" "Sorries"
    printf "%-50s %8s %8s\n" "----" "------" "-------"

    for src_dir in "${src_dirs[@]}"; do
        # Scan directory and matching root file (e.g. GaussianField/ and GaussianField.lean)
        local files=()
        if [ -d "$dir/$src_dir" ]; then
            while IFS= read -r f; do files+=("$f"); done < <(find "$dir/$src_dir" -name '*.lean' 2>/dev/null | sort)
        fi
        [ -f "$dir/$src_dir.lean" ] && files+=("$dir/$src_dir.lean")

        for file in "${files[@]}"; do
            local rel="${file#$dir/}"
            local axioms
            axioms=$(count_file "$file" '^axiom ')
            local sorries
            sorries=$(count_file "$file" 'sorry')

            if [ "$axioms" -gt 0 ] || [ "$sorries" -gt 0 ]; then
                printf "%-50s %8d %8d\n" "$rel" "$axioms" "$sorries"
                total_axioms=$((total_axioms + axioms))
                total_sorries=$((total_sorries + sorries))
            fi
        done
    done

    printf "%-50s %8s %8s\n" "" "------" "-------"
    printf "%-50s %8d %8d\n" "TOTAL" "$total_axioms" "$total_sorries"
}

count_in_dir "$PPHI2_DIR" "pphi2" "Pphi2"

if [ -d "$GF_DIR" ]; then
    count_in_dir "$GF_DIR" "gaussian-field" "GaussianField" "HeatKernel" "Lattice" "SchwartzNuclear"
else
    echo ""
    echo -e "${RED}gaussian-field not found at $GF_DIR${NC}"
fi
