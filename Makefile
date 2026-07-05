CXX      ?= g++
TARGET   := maf
SRC      := maf_combined.cpp
LIST     := pace26_heuristic_pub_v2.lst

# Release flags for the optil.io judge (Haswell Xeon, self-contained binary).
CXXFLAGS := -std=c++17 -O3 -march=haswell -mtune=haswell \
            -funroll-loops -fomit-frame-pointer -flto -DNDEBUG -pipe -static

# Flags tuned for the local build CPU — use only for local speed tests, never
# for a binary that will run on the judge.
NATIVE_FLAGS := -std=c++17 -O3 -march=native -mtune=native \
                -funroll-loops -fomit-frame-pointer -flto -DNDEBUG -pipe

.PHONY: all native run debug clean branch branch-run combined combined-run

all: $(TARGET)

$(TARGET): $(SRC)
	$(CXX) $(CXXFLAGS) -o $@ $<

native: $(SRC)
	$(CXX) $(NATIVE_FLAGS) -o $(TARGET) $<

run: all
	./stride run -s ./$(TARGET) -i $(LIST)

debug: $(SRC)
	$(CXX) -std=c++17 -O1 -g -Wall -Wextra -fsanitize=address,undefined \
	    -o $(TARGET)_debug $<

clean:
	rm -f $(TARGET) $(TARGET)_debug
