PYTHON=python
SPELL=$(PYTHON) spell_cli.py

all: family courses hobbies father hard1 hard5 yago10_2 yago10_19 owl2bench1 owl2bench3 owl2bench4 color1 color2 color3 color4 color-alt-1 color-alt-2 color-alt-3 color-alt-4 color-alt-5 color-alt-6 color-alt-9 color-alt-10 conj1 conj2 conj3 conj4 debug

family:
	$(SPELL) tests/family-example/family.owl tests/family-example/P.txt tests/family-example/N.txt

courses:
	$(SPELL) tests/courses-example/courses.owl tests/courses-example/P.txt tests/courses-example/N.txt

hobbies:
	$(SPELL) tests/hobbies-example/hobbies.owl tests/hobbies-example/P.txt tests/hobbies-example/N.txt

father:
	$(SPELL) tests/father-example/father.owl tests/father-example/P.txt tests/father-example/N.txt

hard1:
	$(SPELL) tests/test-hard-deep-conj-1/owl/data/test-hard-deep-conj-1.owl tests/test-hard-deep-conj-1/owl/lp/1/pos.txt tests/test-hard-deep-conj-1/owl/lp/1/neg.txt

hard5:
	$(SPELL) tests/test-hard-deep-conj-5/owl/data/test-hard-deep-conj-5.owl tests/test-hard-deep-conj-5/owl/lp/1/pos.txt tests/test-hard-deep-conj-5/owl/lp/1/neg.txt

yago10_2:
	$(SPELL) tests/yago-gen-test-10-2/owl/data/yago-gen-test-10-2.owl tests/yago-gen-test-10-2/owl/lp/1/pos.txt tests/yago-gen-test-10-2/owl/lp/1/neg.txt

yago10_19:
	$(SPELL) tests/yago-gen-test-10-19/owl/data/yago-gen-test-10-19.owl tests/yago-gen-test-10-19/owl/lp/1/pos.txt tests/yago-gen-test-10-19/owl/lp/1/neg.txt

owl2bench1:
	$(SPELL) tests/owl2bench-1/owl/data/owl2bench-1.owl tests/owl2bench-1/owl/lp/1/pos.txt tests/owl2bench-1/owl/lp/1/neg.txt

owl2bench3:
	$(SPELL) tests/owl2bench-3/owl/data/owl2bench-3.owl tests/owl2bench-3/owl/lp/1/pos.txt tests/owl2bench-3/owl/lp/1/neg.txt

owl2bench4:
	$(SPELL) tests/owl2bench-4/owl/data/owl2bench-4.owl tests/owl2bench-4/owl/lp/1/pos.txt tests/owl2bench-4/owl/lp/1/neg.txt

color1:
	$(SPELL) tests/color-example/color-depth1.owl tests/color-example/P.txt tests/color-example/N-depth1.txt

color2:
	$(SPELL) tests/color-example/color-depth2.owl tests/color-example/P.txt tests/color-example/N-depth2.txt

color3:
	$(SPELL) tests/color-example/color-depth3.owl tests/color-example/P.txt tests/color-example/N-depth3.txt

color4:
	$(SPELL) tests/color-example/color-depth4.owl tests/color-example/P.txt tests/color-example/N-depth4.txt

color-alt-1:
	$(SPELL) tests/color-example/color-alt-depth1.owl tests/color-example/P.txt tests/color-example/N.txt

color-alt-2:
	$(SPELL) tests/color-example/color-alt-depth2.owl tests/color-example/P.txt tests/color-example/N.txt

color-alt-3:
	$(SPELL) tests/color-example/color-alt-depth3.owl tests/color-example/P.txt tests/color-example/N.txt

color-alt-4:
	$(SPELL) tests/color-example/color-alt-depth4.owl tests/color-example/P.txt tests/color-example/N.txt

color-alt-5:
	$(SPELL) tests/color-example/color-alt-depth5.owl tests/color-example/P.txt tests/color-example/N.txt

color-alt-6:
	$(SPELL) tests/color-example/color-alt-depth6.owl tests/color-example/P.txt tests/color-example/N.txt

conj1:
	$(SPELL) tests/conjunction-example/conj1.owl tests/conjunction-example/P.txt tests/conjunction-example/N.txt

conj2:
	$(SPELL) tests/conjunction-example/conj2.owl tests/conjunction-example/P.txt tests/conjunction-example/N.txt

conj3:
	$(SPELL) tests/conjunction-example/conj3.owl tests/conjunction-example/P.txt tests/conjunction-example/N.txt

conj4:
	$(SPELL) tests/conjunction-example/conj4.owl tests/conjunction-example/P.txt tests/conjunction-example/N.txt

debug:
	$(SPELL) tests/debug-example/debug.owl tests/debug-example/P.txt tests/debug-example/N.txt

