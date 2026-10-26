import V185TrunkScan23Chunk0301

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1786939 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 4, 2]
def baseStart_1786939 : Nat := 118140960795 + 1786939 * 2 ^ 59
def prefixEnd_1786939 : Nat := 4983230072969 + 3 ^ 40 * 1786939 * 2
def baseEnd_1786939 : Nat := 917558607264689326644523

theorem tailTrace_1786939 : CollatzResearch.WordTrace tailWord_1786939 prefixEnd_1786939 917558607264689326644523 := by
  unfold tailWord_1786939
  simp only [CollatzResearch.WordTrace]
  refine ⟨65175019673232662729299871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43450013115488441819533247 65175019673232662729299871)
  ·
    refine ⟨97762529509848994093949807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65175019673232662729299871 97762529509848994093949807)
    ·
      refine ⟨146643794264773491140924711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97762529509848994093949807 146643794264773491140924711)
      ·
        refine ⟨219965691397160236711387067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146643794264773491140924711 219965691397160236711387067)
        ·
          refine ⟨329948537095740355067080601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219965691397160236711387067 329948537095740355067080601)
          ·
            refine ⟨247461402821805266300310451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329948537095740355067080601 247461402821805266300310451)
            ·
              refine ⟨371192104232707899450465677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247461402821805266300310451 371192104232707899450465677)
              ·
                refine ⟨139197039087265462293924629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371192104232707899450465677 139197039087265462293924629)
                ·
                  refine ⟨6524861207215568545027717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139197039087265462293924629 6524861207215568545027717)
                  ·
                    refine ⟨1223411476352919102192697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524861207215568545027717 1223411476352919102192697)
                    ·
                      refine ⟨917558607264689326644523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223411476352919102192697 917558607264689326644523)
                      ·
                        rfl

theorem cell23_1786939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4, 2].length) (baseStart_1786939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786939 prefixEnd_1786939 := by exact prefixLift 1786939
  have htrace : WordTrace (prefixWord ++ tailWord_1786939) baseStart_1786939 baseEnd_1786939 := by
    simpa [prefixWord, tailWord_1786939, baseEnd_1786939] using wordTrace_append hprefix tailTrace_1786939
  have hstable : (prefixWord ++ tailWord_1786939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786939).length < 2 ^ (prefixWord ++ tailWord_1786939).sum := by decide
  have hdescent : baseEnd_1786939 < baseStart_1786939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786952 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1786952 : Nat := 118140960795 + 1786952 * 2 ^ 59
def prefixEnd_1786952 : Nat := 4983230072969 + 3 ^ 40 * 1786952 * 2
def baseEnd_1786952 : Nat := 917565282513197775781963

theorem tailTrace_1786952 : CollatzResearch.WordTrace tailWord_1786952 prefixEnd_1786952 917565282513197775781963 := by
  unfold tailWord_1786952
  simp only [CollatzResearch.WordTrace]
  refine ⟨32587746911092782974761555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43450329214790377299682073 32587746911092782974761555)
  ·
    refine ⟨48881620366639174462142333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32587746911092782974761555 48881620366639174462142333)
    ·
      refine ⟨18330607637489690423303375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48881620366639174462142333 18330607637489690423303375)
      ·
        refine ⟨27495911456234535634955063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18330607637489690423303375 27495911456234535634955063)
        ·
          refine ⟨41243867184351803452432595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27495911456234535634955063 41243867184351803452432595)
          ·
            refine ⟨61865800776527705178648893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41243867184351803452432595 61865800776527705178648893)
            ·
              refine ⟨23199675291197889441993335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61865800776527705178648893 23199675291197889441993335)
              ·
                refine ⟨34799512936796834162990003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23199675291197889441993335 34799512936796834162990003)
                ·
                  refine ⟨52199269405195251244485005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34799512936796834162990003 52199269405195251244485005)
                  ·
                    refine ⟨19574726026948219216681877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52199269405195251244485005 19574726026948219216681877)
                    ·
                      refine ⟨917565282513197775781963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19574726026948219216681877 917565282513197775781963)
                      ·
                        rfl

theorem cell23_1786952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1786952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786952 prefixEnd_1786952 := by exact prefixLift 1786952
  have htrace : WordTrace (prefixWord ++ tailWord_1786952) baseStart_1786952 baseEnd_1786952 := by
    simpa [prefixWord, tailWord_1786952, baseEnd_1786952] using wordTrace_append hprefix tailTrace_1786952
  have hstable : (prefixWord ++ tailWord_1786952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786952).length < 2 ^ (prefixWord ++ tailWord_1786952).sum := by decide
  have hdescent : baseEnd_1786952 < baseStart_1786952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787050 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1787050 : Nat := 118140960795 + 1787050 * 2 ^ 59
def prefixEnd_1787050 : Nat := 4983230072969 + 3 ^ 40 * 1787050 * 2
def baseEnd_1787050 : Nat := 917615603617338392356513

theorem tailTrace_1787050 : CollatzResearch.WordTrace tailWord_1787050 prefixEnd_1787050 917615603617338392356513 := by
  unfold tailWord_1787050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294767043957632171647651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43452712117220352457727069 16294767043957632171647651)
  ·
    refine ⟨24442150565936448257471477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16294767043957632171647651 24442150565936448257471477)
    ·
      refine ⟨2291451615556542024137951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24442150565936448257471477 2291451615556542024137951)
      ·
        refine ⟨3437177423334813036206927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291451615556542024137951 3437177423334813036206927)
        ·
          refine ⟨5155766135002219554310391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437177423334813036206927 5155766135002219554310391)
          ·
            refine ⟨7733649202503329331465587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155766135002219554310391 7733649202503329331465587)
            ·
              refine ⟨11600473803754993997198381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733649202503329331465587 11600473803754993997198381)
              ·
                refine ⟨4350177676408122748949393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11600473803754993997198381 4350177676408122748949393)
                ·
                  refine ⟨3262633257306092061712045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350177676408122748949393 3262633257306092061712045)
                  ·
                    refine ⟨1223487471489784523142017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262633257306092061712045 1223487471489784523142017)
                    ·
                      refine ⟨917615603617338392356513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223487471489784523142017 917615603617338392356513)
                      ·
                        rfl

theorem cell23_1787050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1787050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787050 prefixEnd_1787050 := by exact prefixLift 1787050
  have htrace : WordTrace (prefixWord ++ tailWord_1787050) baseStart_1787050 baseEnd_1787050 := by
    simpa [prefixWord, tailWord_1787050, baseEnd_1787050] using wordTrace_append hprefix tailTrace_1787050
  have hstable : (prefixWord ++ tailWord_1787050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787050).length < 2 ^ (prefixWord ++ tailWord_1787050).sum := by decide
  have hdescent : baseEnd_1787050 < baseStart_1787050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787059 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_1787059 : Nat := 118140960795 + 1787059 * 2 ^ 59
def prefixEnd_1787059 : Nat := 4983230072969 + 3 ^ 40 * 1787059 * 2
def baseEnd_1787059 : Nat := 917620224943228857143971

theorem tailTrace_1787059 : CollatzResearch.WordTrace tailWord_1787059 prefixEnd_1787059 917620224943228857143971 := by
  unfold tailWord_1787059
  simp only [CollatzResearch.WordTrace]
  refine ⟨65179396432797923223668231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43452930955198615482445487 65179396432797923223668231)
  ·
    refine ⟨97769094649196884835502347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65179396432797923223668231 97769094649196884835502347)
    ·
      refine ⟨146653641973795327253253521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97769094649196884835502347 146653641973795327253253521)
      ·
        refine ⟨109990231480346495439940141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146653641973795327253253521 109990231480346495439940141)
        ·
          refine ⟨41246336805129935789977553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109990231480346495439940141 41246336805129935789977553)
          ·
            refine ⟨30934752603847451842483165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41246336805129935789977553 30934752603847451842483165)
            ·
              refine ⟨11600532226442794440931187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30934752603847451842483165 11600532226442794440931187)
              ·
                refine ⟨17400798339664191661396781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600532226442794440931187 17400798339664191661396781)
                ·
                  refine ⟨6525299377374071873023793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17400798339664191661396781 6525299377374071873023793)
                  ·
                    refine ⟨4893974533030553904767845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525299377374071873023793 4893974533030553904767845)
                    ·
                      refine ⟨917620224943228857143971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4893974533030553904767845 917620224943228857143971)
                      ·
                        rfl

theorem cell23_1787059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_1787059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787059 prefixEnd_1787059 := by exact prefixLift 1787059
  have htrace : WordTrace (prefixWord ++ tailWord_1787059) baseStart_1787059 baseEnd_1787059 := by
    simpa [prefixWord, tailWord_1787059, baseEnd_1787059] using wordTrace_append hprefix tailTrace_1787059
  have hstable : (prefixWord ++ tailWord_1787059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787059).length < 2 ^ (prefixWord ++ tailWord_1787059).sum := by decide
  have hdescent : baseEnd_1787059 < baseStart_1787059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787063 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_1787063 : Nat := 118140960795 + 1787063 * 2 ^ 59
def prefixEnd_1787063 : Nat := 4983230072969 + 3 ^ 40 * 1787063 * 2
def baseEnd_1787063 : Nat := 917622278865846841493953

theorem tailTrace_1787063 : CollatzResearch.WordTrace tailWord_1787063 prefixEnd_1787063 917622278865846841493953 := by
  unfold tailWord_1787063
  simp only [CollatzResearch.WordTrace]
  refine ⟨65179542324783431906813843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43453028216522287937875895 65179542324783431906813843)
  ·
    refine ⟨97769313487175147860220765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65179542324783431906813843 97769313487175147860220765)
    ·
      refine ⟨36663492557690680447582787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97769313487175147860220765 36663492557690680447582787)
      ·
        refine ⟨54995238836536020671374181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663492557690680447582787 54995238836536020671374181)
        ·
          refine ⟨10311607281850503875882659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54995238836536020671374181 10311607281850503875882659)
          ·
            refine ⟨15467410922775755813823989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311607281850503875882659 15467410922775755813823989)
            ·
              refine ⟨1450069774010227107545999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15467410922775755813823989 1450069774010227107545999)
              ·
                refine ⟨2175104661015340661318999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450069774010227107545999 2175104661015340661318999)
                ·
                  refine ⟨3262656991523010991978499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175104661015340661318999 3262656991523010991978499)
                  ·
                    refine ⟨4893985487284516487967749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3262656991523010991978499 4893985487284516487967749)
                    ·
                      refine ⟨917622278865846841493953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4893985487284516487967749 917622278865846841493953)
                      ·
                        rfl

theorem cell23_1787063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_1787063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787063 prefixEnd_1787063 := by exact prefixLift 1787063
  have htrace : WordTrace (prefixWord ++ tailWord_1787063) baseStart_1787063 baseEnd_1787063 := by
    simpa [prefixWord, tailWord_1787063, baseEnd_1787063] using wordTrace_append hprefix tailTrace_1787063
  have hstable : (prefixWord ++ tailWord_1787063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787063).length < 2 ^ (prefixWord ++ tailWord_1787063).sum := by decide
  have hdescent : baseEnd_1787063 < baseStart_1787063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787093 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1787093 : Nat := 118140960795 + 1787093 * 2 ^ 59
def prefixEnd_1787093 : Nat := 4983230072969 + 3 ^ 40 * 1787093 * 2
def baseEnd_1787093 : Nat := 917637683285481724118815

theorem tailTrace_1787093 : CollatzResearch.WordTrace tailWord_1787093 prefixEnd_1787093 917637683285481724118815 := by
  unfold tailWord_1787093
  simp only [CollatzResearch.WordTrace]
  refine ⟨65180636514674747030405933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43453757676449831353603955 65180636514674747030405933)
  ·
    refine ⟨24442738693003030136402225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65180636514674747030405933 24442738693003030136402225)
    ·
      refine ⟨18332054019752272602301669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24442738693003030136402225 18332054019752272602301669)
      ·
        refine ⟨3437260128703551112931563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18332054019752272602301669 3437260128703551112931563)
        ·
          refine ⟨5155890193055326669397345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437260128703551112931563 5155890193055326669397345)
          ·
            refine ⟨3866917644791495002048009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155890193055326669397345 3866917644791495002048009)
            ·
              refine ⟨2900188233593621251536007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866917644791495002048009 2900188233593621251536007)
              ·
                refine ⟨4350282350390431877304011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900188233593621251536007 4350282350390431877304011)
                ·
                  refine ⟨6525423525585647815956017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350282350390431877304011 6525423525585647815956017)
                  ·
                    refine ⟨4894067644189235861967013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525423525585647815956017 4894067644189235861967013)
                    ·
                      refine ⟨917637683285481724118815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4894067644189235861967013 917637683285481724118815)
                      ·
                        rfl

theorem cell23_1787093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1787093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787093 prefixEnd_1787093 := by exact prefixLift 1787093
  have htrace : WordTrace (prefixWord ++ tailWord_1787093) baseStart_1787093 baseEnd_1787093 := by
    simpa [prefixWord, tailWord_1787093, baseEnd_1787093] using wordTrace_append hprefix tailTrace_1787093
  have hstable : (prefixWord ++ tailWord_1787093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787093).length < 2 ^ (prefixWord ++ tailWord_1787093).sum := by decide
  have hdescent : baseEnd_1787093 < baseStart_1787093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787117 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1787117 : Nat := 118140960795 + 1787117 * 2 ^ 59
def prefixEnd_1787117 : Nat := 4983230072969 + 3 ^ 40 * 1787117 * 2
def baseEnd_1787117 : Nat := 917650006821189630218705

theorem tailTrace_1787117 : CollatzResearch.WordTrace tailWord_1787117 prefixEnd_1787117 917650006821189630218705 := by
  unfold tailWord_1787117
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181511866587799129279605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43454341244391866086186403 65181511866587799129279605)
  ·
    refine ⟨6110766737492606168369963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65181511866587799129279605 6110766737492606168369963)
    ·
      refine ⟨9166150106238909252554945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110766737492606168369963 9166150106238909252554945)
      ·
        refine ⟨6874612579679181939416209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9166150106238909252554945 6874612579679181939416209)
        ·
          refine ⟨5155959434759386454562157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6874612579679181939416209 5155959434759386454562157)
          ·
            refine ⟨1933484788034769920460809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5155959434759386454562157 1933484788034769920460809)
            ·
              refine ⟨1450113591026077440345607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933484788034769920460809 1450113591026077440345607)
              ·
                refine ⟨2175170386539116160518411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450113591026077440345607 2175170386539116160518411)
                ·
                  refine ⟨3262755579808674240777617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175170386539116160518411 3262755579808674240777617)
                  ·
                    refine ⟨2447066684856505680583213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3262755579808674240777617 2447066684856505680583213)
                    ·
                      refine ⟨917650006821189630218705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447066684856505680583213 917650006821189630218705)
                      ·
                        rfl

theorem cell23_1787117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1787117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787117 prefixEnd_1787117 := by exact prefixLift 1787117
  have htrace : WordTrace (prefixWord ++ tailWord_1787117) baseStart_1787117 baseEnd_1787117 := by
    simpa [prefixWord, tailWord_1787117, baseEnd_1787117] using wordTrace_append hprefix tailTrace_1787117
  have hstable : (prefixWord ++ tailWord_1787117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787117).length < 2 ^ (prefixWord ++ tailWord_1787117).sum := by decide
  have hdescent : baseEnd_1787117 < baseStart_1787117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787129 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_1787129 : Nat := 118140960795 + 1787129 * 2 ^ 59
def prefixEnd_1787129 : Nat := 4983230072969 + 3 ^ 40 * 1787129 * 2
def baseEnd_1787129 : Nat := 305885389529681194422883

theorem tailTrace_1787129 : CollatzResearch.WordTrace tailWord_1787129 prefixEnd_1787129 305885389529681194422883 := by
  unfold tailWord_1787129
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181949542544325178716441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43454633028362883452477627 65181949542544325178716441)
  ·
    refine ⟨48886462156908243884037331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65181949542544325178716441 48886462156908243884037331)
    ·
      refine ⟨73329693235362365826055997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886462156908243884037331 73329693235362365826055997)
      ·
        refine ⟨27498634963260887184770999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73329693235362365826055997 27498634963260887184770999)
        ·
          refine ⟨41247952444891330777156499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27498634963260887184770999 41247952444891330777156499)
          ·
            refine ⟨61871928667336996165734749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41247952444891330777156499 61871928667336996165734749)
            ·
              refine ⟨23201973250251373562150531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61871928667336996165734749 23201973250251373562150531)
              ·
                refine ⟨34802959875377060343225797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23201973250251373562150531 34802959875377060343225797)
                ·
                  refine ⟨6525554976633198814354837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34802959875377060343225797 6525554976633198814354837)
                  ·
                    refine ⟨305885389529681194422883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6525554976633198814354837 305885389529681194422883)
                    ·
                      rfl

theorem cell23_1787129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_1787129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787129 prefixEnd_1787129 := by exact prefixLift 1787129
  have htrace : WordTrace (prefixWord ++ tailWord_1787129) baseStart_1787129 baseEnd_1787129 := by
    simpa [prefixWord, tailWord_1787129, baseEnd_1787129] using wordTrace_append hprefix tailTrace_1787129
  have hstable : (prefixWord ++ tailWord_1787129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787129).length < 2 ^ (prefixWord ++ tailWord_1787129).sum := by decide
  have hdescent : baseEnd_1787129 < baseStart_1787129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787204 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1787204 : Nat := 118140960795 + 1787204 * 2 ^ 59
def prefixEnd_1787204 : Nat := 4983230072969 + 3 ^ 40 * 1787204 * 2
def baseEnd_1787204 : Nat := 917694679638130789830805

theorem tailTrace_1787204 : CollatzResearch.WordTrace tailWord_1787204 prefixEnd_1787204 917694679638130789830805 := by
  unfold tailWord_1787204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592342508636306493848333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43456456678181741991797777 32592342508636306493848333)
  ·
    refine ⟨12222128440738614935193125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32592342508636306493848333 12222128440738614935193125)
    ·
      refine ⟨2291649082638490300348711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12222128440738614935193125 2291649082638490300348711)
      ·
        refine ⟨3437473623957735450523067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291649082638490300348711 3437473623957735450523067)
        ·
          refine ⟨5156210435936603175784601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437473623957735450523067 5156210435936603175784601)
          ·
            refine ⟨3867157826952452381838451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156210435936603175784601 3867157826952452381838451)
            ·
              refine ⟨5800736740428678572757677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867157826952452381838451 5800736740428678572757677)
              ·
                refine ⟨2175276277660754464784129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800736740428678572757677 2175276277660754464784129)
                ·
                  refine ⟨1631457208245565848588097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2175276277660754464784129 1631457208245565848588097)
                  ·
                    refine ⟨1223592906184174386441073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631457208245565848588097 1223592906184174386441073)
                    ·
                      refine ⟨917694679638130789830805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223592906184174386441073 917694679638130789830805)
                      ·
                        rfl

theorem cell23_1787204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1787204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787204 prefixEnd_1787204 := by exact prefixLift 1787204
  have htrace : WordTrace (prefixWord ++ tailWord_1787204) baseStart_1787204 baseEnd_1787204 := by
    simpa [prefixWord, tailWord_1787204, baseEnd_1787204] using wordTrace_append hprefix tailTrace_1787204
  have hstable : (prefixWord ++ tailWord_1787204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787204).length < 2 ^ (prefixWord ++ tailWord_1787204).sum := by decide
  have hdescent : baseEnd_1787204 < baseStart_1787204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787223 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 2, 5]
def baseStart_1787223 : Nat := 118140960795 + 1787223 * 2 ^ 59
def prefixEnd_1787223 : Nat := 4983230072969 + 3 ^ 40 * 1787223 * 2
def baseEnd_1787223 : Nat := 305901478590188738497739

theorem tailTrace_1787223 : CollatzResearch.WordTrace tailWord_1787223 prefixEnd_1787223 305901478590188738497739 := by
  unfold tailWord_1787223
  simp only [CollatzResearch.WordTrace]
  refine ⟨65185378004203779232638323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43456918669469186155092215 65185378004203779232638323)
  ·
    refine ⟨97778067006305668848957485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65185378004203779232638323 97778067006305668848957485)
    ·
      refine ⟨36666775127364625818359057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97778067006305668848957485 36666775127364625818359057)
      ·
        refine ⟨27500081345523469363769293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36666775127364625818359057 27500081345523469363769293)
        ·
          refine ⟨10312530504571301011413485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27500081345523469363769293 10312530504571301011413485)
          ·
            refine ⟨3867198939214237879280057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10312530504571301011413485 3867198939214237879280057)
            ·
              refine ⟨2900399204410678409460043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867198939214237879280057 2900399204410678409460043)
              ·
                refine ⟨4350598806616017614190065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900399204410678409460043 4350598806616017614190065)
                ·
                  refine ⟨3262949104962013210642549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350598806616017614190065 3262949104962013210642549)
                  ·
                    refine ⟨305901478590188738497739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3262949104962013210642549 305901478590188738497739)
                    ·
                      rfl

theorem cell23_1787223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_1787223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787223 prefixEnd_1787223 := by exact prefixLift 1787223
  have htrace : WordTrace (prefixWord ++ tailWord_1787223) baseStart_1787223 baseEnd_1787223 := by
    simpa [prefixWord, tailWord_1787223, baseEnd_1787223] using wordTrace_append hprefix tailTrace_1787223
  have hstable : (prefixWord ++ tailWord_1787223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787223).length < 2 ^ (prefixWord ++ tailWord_1787223).sum := by decide
  have hdescent : baseEnd_1787223 < baseStart_1787223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787226 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1787226 : Nat := 118140960795 + 1787226 * 2 ^ 59
def prefixEnd_1787226 : Nat := 4983230072969 + 3 ^ 40 * 1787226 * 2
def baseEnd_1787226 : Nat := 917705976212529703755703

theorem tailTrace_1787226 : CollatzResearch.WordTrace tailWord_1787226 prefixEnd_1787226 917705976212529703755703 := by
  unfold tailWord_1787226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296371855798227686249383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43456991615461940496665021 16296371855798227686249383)
  ·
    refine ⟨24444557783697341529374075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16296371855798227686249383 24444557783697341529374075)
    ·
      refine ⟨36666836675546012294061113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24444557783697341529374075 36666836675546012294061113)
      ·
        refine ⟨27500127506659509220545835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36666836675546012294061113 27500127506659509220545835)
        ·
          refine ⟨41250191259989263830818753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27500127506659509220545835 41250191259989263830818753)
          ·
            refine ⟨30937643444991947873114065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41250191259989263830818753 30937643444991947873114065)
            ·
              refine ⟨23203232583743960904835549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30937643444991947873114065 23203232583743960904835549)
              ·
                refine ⟨8701212218903985339313331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23203232583743960904835549 8701212218903985339313331)
                ·
                  refine ⟨13051818328355978008969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701212218903985339313331 13051818328355978008969997)
                  ·
                    refine ⟨4894431873133491753363749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13051818328355978008969997 4894431873133491753363749)
                    ·
                      refine ⟨917705976212529703755703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4894431873133491753363749 917705976212529703755703)
                      ·
                        rfl

theorem cell23_1787226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1787226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787226 prefixEnd_1787226 := by exact prefixLift 1787226
  have htrace : WordTrace (prefixWord ++ tailWord_1787226) baseStart_1787226 baseEnd_1787226 := by
    simpa [prefixWord, tailWord_1787226, baseEnd_1787226] using wordTrace_append hprefix tailTrace_1787226
  have hstable : (prefixWord ++ tailWord_1787226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787226).length < 2 ^ (prefixWord ++ tailWord_1787226).sum := by decide
  have hdescent : baseEnd_1787226 < baseStart_1787226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787343 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 4, 4]
def baseStart_1787343 : Nat := 118140960795 + 1787343 * 2 ^ 59
def prefixEnd_1787343 : Nat := 4983230072969 + 3 ^ 40 * 1787343 * 2
def baseEnd_1787343 : Nat := 305922017816368581997555

theorem tailTrace_1787343 : CollatzResearch.WordTrace tailWord_1787343 prefixEnd_1787343 305922017816368581997555 := by
  unfold tailWord_1787343
  simp only [CollatzResearch.WordTrace]
  refine ⟨65189754763769039727006683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43459836509179359818004455 65189754763769039727006683)
  ·
    refine ⟨97784632145653559590510025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65189754763769039727006683 97784632145653559590510025)
    ·
      refine ⟨73338474109240169692882519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97784632145653559590510025 73338474109240169692882519)
      ·
        refine ⟨110007711163860254539323779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73338474109240169692882519 110007711163860254539323779)
        ·
          refine ⟨165011566745790381808985669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110007711163860254539323779 165011566745790381808985669)
          ·
            refine ⟨30939668764835696589184813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165011566745790381808985669 30939668764835696589184813)
            ·
              refine ⟨11602375786813386220944305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30939668764835696589184813 11602375786813386220944305)
              ·
                refine ⟨8701781840110039665708229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602375786813386220944305 8701781840110039665708229)
                ·
                  refine ⟨1631584095020632437320293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8701781840110039665708229 1631584095020632437320293)
                  ·
                    refine ⟨305922017816368581997555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631584095020632437320293 305922017816368581997555)
                    ·
                      rfl

theorem cell23_1787343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_1787343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787343 prefixEnd_1787343 := by exact prefixLift 1787343
  have htrace : WordTrace (prefixWord ++ tailWord_1787343) baseStart_1787343 baseEnd_1787343 := by
    simpa [prefixWord, tailWord_1787343, baseEnd_1787343] using wordTrace_append hprefix tailTrace_1787343
  have hstable : (prefixWord ++ tailWord_1787343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787343).length < 2 ^ (prefixWord ++ tailWord_1787343).sum := by decide
  have hdescent : baseEnd_1787343 < baseStart_1787343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787353 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1787353 : Nat := 118140960795 + 1787353 * 2 ^ 59
def prefixEnd_1787353 : Nat := 4983230072969 + 3 ^ 40 * 1787353 * 2
def baseEnd_1787353 : Nat := 917771188255650706867619

theorem tailTrace_1787353 : CollatzResearch.WordTrace tailWord_1787353 prefixEnd_1787353 917771188255650706867619 := by
  unfold tailWord_1787353
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190119493732811434870713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43460079662488540956580475 65190119493732811434870713)
  ·
    refine ⟨48892589620299608576153035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65190119493732811434870713 48892589620299608576153035)
    ·
      refine ⟨73338884430449412864229553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48892589620299608576153035 73338884430449412864229553)
      ·
        refine ⟨55004163322837059648172165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73338884430449412864229553 55004163322837059648172165)
        ·
          refine ⟨10313280623031948684032281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55004163322837059648172165 10313280623031948684032281)
          ·
            refine ⟨7734960467273961513024211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313280623031948684032281 7734960467273961513024211)
            ·
              refine ⟨11602440700910942269536317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734960467273961513024211 11602440700910942269536317)
              ·
                refine ⟨4350915262841603351076119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11602440700910942269536317 4350915262841603351076119)
                ·
                  refine ⟨6526372894262405026614179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350915262841603351076119 6526372894262405026614179)
                  ·
                    refine ⟨9789559341393607539921269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526372894262405026614179 9789559341393607539921269)
                    ·
                      refine ⟨917771188255650706867619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9789559341393607539921269 917771188255650706867619)
                      ·
                        rfl

theorem cell23_1787353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1787353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787353 prefixEnd_1787353 := by exact prefixLift 1787353
  have htrace : WordTrace (prefixWord ++ tailWord_1787353) baseStart_1787353 baseEnd_1787353 := by
    simpa [prefixWord, tailWord_1787353, baseEnd_1787353] using wordTrace_append hprefix tailTrace_1787353
  have hstable : (prefixWord ++ tailWord_1787353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787353).length < 2 ^ (prefixWord ++ tailWord_1787353).sum := by decide
  have hdescent : baseEnd_1787353 < baseStart_1787353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787363 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1787363 : Nat := 118140960795 + 1787363 * 2 ^ 59
def prefixEnd_1787363 : Nat := 4983230072969 + 3 ^ 40 * 1787363 * 2
def baseEnd_1787363 : Nat := 917776323062195667742573

theorem tailTrace_1787363 : CollatzResearch.WordTrace tailWord_1787363 prefixEnd_1787363 917776323062195667742573 := by
  unfold tailWord_1787363
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190484223696583142734743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43460322815797722095156495 65190484223696583142734743)
  ·
    refine ⟨97785726335544874714102115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65190484223696583142734743 97785726335544874714102115)
    ·
      refine ⟨146678589503317312071153173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97785726335544874714102115 146678589503317312071153173)
      ·
        refine ⟨6875558882967999003335305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146678589503317312071153173 6875558882967999003335305)
        ·
          refine ⟨5156669162225999252501479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6875558882967999003335305 5156669162225999252501479)
          ·
            refine ⟨7735003743338998878752219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156669162225999252501479 7735003743338998878752219)
            ·
              refine ⟨11602505615008498318128329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735003743338998878752219 11602505615008498318128329)
              ·
                refine ⟨8701879211256373738596247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602505615008498318128329 8701879211256373738596247)
                ·
                  refine ⟨13052818816884560607894371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701879211256373738596247 13052818816884560607894371)
                  ·
                    refine ⟨19579228225326840911841557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052818816884560607894371 19579228225326840911841557)
                    ·
                      refine ⟨917776323062195667742573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19579228225326840911841557 917776323062195667742573)
                      ·
                        rfl

theorem cell23_1787363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1787363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787363 prefixEnd_1787363 := by exact prefixLift 1787363
  have htrace : WordTrace (prefixWord ++ tailWord_1787363) baseStart_1787363 baseEnd_1787363 := by
    simpa [prefixWord, tailWord_1787363, baseEnd_1787363] using wordTrace_append hprefix tailTrace_1787363
  have hstable : (prefixWord ++ tailWord_1787363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787363).length < 2 ^ (prefixWord ++ tailWord_1787363).sum := by decide
  have hdescent : baseEnd_1787363 < baseStart_1787363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787377 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_1787377 : Nat := 118140960795 + 1787377 * 2 ^ 59
def prefixEnd_1787377 : Nat := 4983230072969 + 3 ^ 40 * 1787377 * 2
def baseEnd_1787377 : Nat := 305927837263786204322503

theorem tailTrace_1787377 : CollatzResearch.WordTrace tailWord_1787377 prefixEnd_1787377 305927837263786204322503 := by
  unfold tailWord_1787377
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190994845645863533744385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43460663230430575689162923 65190994845645863533744385)
  ·
    refine ⟨48893246134234397650308289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65190994845645863533744385 48893246134234397650308289)
    ·
      refine ⟨36669934600675798237731217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48893246134234397650308289 36669934600675798237731217)
      ·
        refine ⟨27502450950506848678298413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36669934600675798237731217 27502450950506848678298413)
        ·
          refine ⟨10313419106440068254361905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27502450950506848678298413 10313419106440068254361905)
          ·
            refine ⟨7735064329830051190771429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313419106440068254361905 7735064329830051190771429)
            ·
              refine ⟨1450324561843134598269643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7735064329830051190771429 1450324561843134598269643)
              ·
                refine ⟨2175486842764701897404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450324561843134598269643 2175486842764701897404465)
                ·
                  refine ⟨1631615132073526423053349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2175486842764701897404465 1631615132073526423053349)
                  ·
                    refine ⟨305927837263786204322503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631615132073526423053349 305927837263786204322503)
                    ·
                      rfl

theorem cell23_1787377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_1787377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787377 prefixEnd_1787377 := by exact prefixLift 1787377
  have htrace : WordTrace (prefixWord ++ tailWord_1787377) baseStart_1787377 baseEnd_1787377 := by
    simpa [prefixWord, tailWord_1787377, baseEnd_1787377] using wordTrace_append hprefix tailTrace_1787377
  have hstable : (prefixWord ++ tailWord_1787377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787377).length < 2 ^ (prefixWord ++ tailWord_1787377).sum := by decide
  have hdescent : baseEnd_1787377 < baseStart_1787377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787398 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1787398 : Nat := 118140960795 + 1787398 * 2 ^ 59
def prefixEnd_1787398 : Nat := 4983230072969 + 3 ^ 40 * 1787398 * 2
def baseEnd_1787398 : Nat := 305931431628367676934971

theorem tailTrace_1787398 : CollatzResearch.WordTrace tailWord_1787398 prefixEnd_1787398 305931431628367676934971 := by
  unfold tailWord_1787398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037242524330305753758089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43461173852379856080172565 2037242524330305753758089)
  ·
    refine ⟨1527931893247729315318567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2037242524330305753758089 1527931893247729315318567)
    ·
      refine ⟨2291897839871593972977851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527931893247729315318567 2291897839871593972977851)
      ·
        refine ⟨3437846759807390959466777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291897839871593972977851 3437846759807390959466777)
        ·
          refine ⟨2578385069855543219600083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437846759807390959466777 2578385069855543219600083)
          ·
            refine ⟨3867577604783314829400125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578385069855543219600083 3867577604783314829400125)
            ·
              refine ⟨1450341601793743061025047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3867577604783314829400125 1450341601793743061025047)
              ·
                refine ⟨2175512402690614591537571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450341601793743061025047 2175512402690614591537571)
                ·
                  refine ⟨3263268604035921887306357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175512402690614591537571 3263268604035921887306357)
                  ·
                    refine ⟨305931431628367676934971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3263268604035921887306357 305931431628367676934971)
                    ·
                      rfl

theorem cell23_1787398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1787398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787398 prefixEnd_1787398 := by exact prefixLift 1787398
  have htrace : WordTrace (prefixWord ++ tailWord_1787398) baseStart_1787398 baseEnd_1787398 := by
    simpa [prefixWord, tailWord_1787398, baseEnd_1787398] using wordTrace_append hprefix tailTrace_1787398
  have hstable : (prefixWord ++ tailWord_1787398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787398).length < 2 ^ (prefixWord ++ tailWord_1787398).sum := by decide
  have hdescent : baseEnd_1787398 < baseStart_1787398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787400 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1787400 : Nat := 118140960795 + 1787400 * 2 ^ 59
def prefixEnd_1787400 : Nat := 4983230072969 + 3 ^ 40 * 1787400 * 2
def baseEnd_1787400 : Nat := 917795321846412022979903

theorem tailTrace_1787400 : CollatzResearch.WordTrace tailWord_1787400 prefixEnd_1787400 917795321846412022979903 := by
  unfold tailWord_1787400
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595916862281269230915827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43461222483041692307887769 32595916862281269230915827)
  ·
    refine ⟨48893875293421903846373741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595916862281269230915827 48893875293421903846373741)
    ·
      refine ⟨18335203235033213942390153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48893875293421903846373741 18335203235033213942390153)
      ·
        refine ⟨13751402426274910456792615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18335203235033213942390153 13751402426274910456792615)
        ·
          refine ⟨20627103639412365685188923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751402426274910456792615 20627103639412365685188923)
          ·
            refine ⟨30940655459118548527783385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20627103639412365685188923 30940655459118548527783385)
            ·
              refine ⟨23205491594338911395837539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30940655459118548527783385 23205491594338911395837539)
              ·
                refine ⟨34808237391508367093756309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205491594338911395837539 34808237391508367093756309)
                ·
                  refine ⟨1631636127726954707519827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34808237391508367093756309 1631636127726954707519827)
                  ·
                    refine ⟨2447454191590432061279741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631636127726954707519827 2447454191590432061279741)
                    ·
                      refine ⟨917795321846412022979903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447454191590432061279741 917795321846412022979903)
                      ·
                        rfl

theorem cell23_1787400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1787400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787400 prefixEnd_1787400 := by exact prefixLift 1787400
  have htrace : WordTrace (prefixWord ++ tailWord_1787400) baseStart_1787400 baseEnd_1787400 := by
    simpa [prefixWord, tailWord_1787400, baseEnd_1787400] using wordTrace_append hprefix tailTrace_1787400
  have hstable : (prefixWord ++ tailWord_1787400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787400).length < 2 ^ (prefixWord ++ tailWord_1787400).sum := by decide
  have hdescent : baseEnd_1787400 < baseStart_1787400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787404 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_1787404 : Nat := 118140960795 + 1787404 * 2 ^ 59
def prefixEnd_1787404 : Nat := 4983230072969 + 3 ^ 40 * 1787404 * 2
def baseEnd_1787404 : Nat := 917797375769030007329885

theorem tailTrace_1787404 : CollatzResearch.WordTrace tailWord_1787404 prefixEnd_1787404 917797375769030007329885 := by
  unfold tailWord_1787404
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595989808274023572488633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43461319744365364763318177 32595989808274023572488633)
  ·
    refine ⟨24446992356205517679366475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32595989808274023572488633 24446992356205517679366475)
    ·
      refine ⟨36670488534308276519049713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24446992356205517679366475 36670488534308276519049713)
      ·
        refine ⟨27502866400731207389287285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36670488534308276519049713 27502866400731207389287285)
        ·
          refine ⟨2578393725068550692745683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27502866400731207389287285 2578393725068550692745683)
          ·
            refine ⟨3867590587602826039118525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578393725068550692745683 3867590587602826039118525)
            ·
              refine ⟨1450346470351059764669447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3867590587602826039118525 1450346470351059764669447)
              ·
                refine ⟨2175519705526589647004171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450346470351059764669447 2175519705526589647004171)
                ·
                  refine ⟨3263279558289884470506257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175519705526589647004171 3263279558289884470506257)
                  ·
                    refine ⟨2447459668717413352879693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263279558289884470506257 2447459668717413352879693)
                    ·
                      refine ⟨917797375769030007329885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447459668717413352879693 917797375769030007329885)
                      ·
                        rfl

theorem cell23_1787404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_1787404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787404 prefixEnd_1787404 := by exact prefixLift 1787404
  have htrace : WordTrace (prefixWord ++ tailWord_1787404) baseStart_1787404 baseEnd_1787404 := by
    simpa [prefixWord, tailWord_1787404, baseEnd_1787404] using wordTrace_append hprefix tailTrace_1787404
  have hstable : (prefixWord ++ tailWord_1787404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787404).length < 2 ^ (prefixWord ++ tailWord_1787404).sum := by decide
  have hdescent : baseEnd_1787404 < baseStart_1787404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787423 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1787423 : Nat := 118140960795 + 1787423 * 2 ^ 59
def prefixEnd_1787423 : Nat := 4983230072969 + 3 ^ 40 * 1787423 * 2
def baseEnd_1787423 : Nat := 917807131901465432992297

theorem tailTrace_1787423 : CollatzResearch.WordTrace tailWord_1787423 prefixEnd_1787423 917807131901465432992297 := by
  unfold tailWord_1787423
  simp only [CollatzResearch.WordTrace]
  refine ⟨65192672603479213389918923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43461781735652808926612615 65192672603479213389918923)
  ·
    refine ⟨97789008905218820084878385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65192672603479213389918923 97789008905218820084878385)
    ·
      refine ⟨73341756678914115063658789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97789008905218820084878385 73341756678914115063658789)
      ·
        refine ⟨13751579377296396574436023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73341756678914115063658789 13751579377296396574436023)
        ·
          refine ⟨20627369065944594861654035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751579377296396574436023 20627369065944594861654035)
          ·
            refine ⟨30941053598916892292481053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20627369065944594861654035 30941053598916892292481053)
            ·
              refine ⟨11602895099593834609680395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30941053598916892292481053 11602895099593834609680395)
              ·
                refine ⟨17404342649390751914520593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602895099593834609680395 17404342649390751914520593)
                ·
                  refine ⟨13053256987043063935890445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17404342649390751914520593 13053256987043063935890445)
                  ·
                    refine ⟨4894971370141148975958917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13053256987043063935890445 4894971370141148975958917)
                    ·
                      refine ⟨917807131901465432992297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4894971370141148975958917 917807131901465432992297)
                      ·
                        rfl

theorem cell23_1787423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1787423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787423 prefixEnd_1787423 := by exact prefixLift 1787423
  have htrace : WordTrace (prefixWord ++ tailWord_1787423) baseStart_1787423 baseEnd_1787423 := by
    simpa [prefixWord, tailWord_1787423, baseEnd_1787423] using wordTrace_append hprefix tailTrace_1787423
  have hstable : (prefixWord ++ tailWord_1787423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787423).length < 2 ^ (prefixWord ++ tailWord_1787423).sum := by decide
  have hdescent : baseEnd_1787423 < baseStart_1787423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787457 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1787457 : Nat := 118140960795 + 1787457 * 2 ^ 59
def prefixEnd_1787457 : Nat := 4983230072969 + 3 ^ 40 * 1787457 * 2
def baseEnd_1787457 : Nat := 917824590243718299967141

theorem tailTrace_1787457 : CollatzResearch.WordTrace tailWord_1787457 prefixEnd_1787457 917824590243718299967141 := by
  unfold tailWord_1787457
  simp only [CollatzResearch.WordTrace]
  refine ⟨65193912685356037196656625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43462608456904024797771083 65193912685356037196656625)
  ·
    refine ⟨48895434514017027897492469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65193912685356037196656625 48895434514017027897492469)
    ·
      refine ⟨4583946985689096365389919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48895434514017027897492469 4583946985689096365389919)
      ·
        refine ⟨6875920478533644548084879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583946985689096365389919 6875920478533644548084879)
        ·
          refine ⟨10313880717800466822127319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875920478533644548084879 10313880717800466822127319)
          ·
            refine ⟨15470821076700700233190979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313880717800466822127319 15470821076700700233190979)
            ·
              refine ⟨23206231615051050349786469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470821076700700233190979 23206231615051050349786469)
              ·
                refine ⟨4351168427822071940584963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23206231615051050349786469 4351168427822071940584963)
                ·
                  refine ⟨6526752641733107910877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351168427822071940584963 6526752641733107910877445)
                  ·
                    refine ⟨1223766120324957733289521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526752641733107910877445 1223766120324957733289521)
                    ·
                      refine ⟨917824590243718299967141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223766120324957733289521 917824590243718299967141)
                      ·
                        rfl

theorem cell23_1787457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1787457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787457 prefixEnd_1787457 := by exact prefixLift 1787457
  have htrace : WordTrace (prefixWord ++ tailWord_1787457) baseStart_1787457 baseEnd_1787457 := by
    simpa [prefixWord, tailWord_1787457, baseEnd_1787457] using wordTrace_append hprefix tailTrace_1787457
  have hstable : (prefixWord ++ tailWord_1787457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787457).length < 2 ^ (prefixWord ++ tailWord_1787457).sum := by decide
  have hdescent : baseEnd_1787457 < baseStart_1787457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787474 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_1787474 : Nat := 118140960795 + 1787474 * 2 ^ 59
def prefixEnd_1787474 : Nat := 4983230072969 + 3 ^ 40 * 1787474 * 2
def baseEnd_1787474 : Nat := 917833319414844733454563

theorem tailTrace_1787474 : CollatzResearch.WordTrace tailWord_1787474 prefixEnd_1787474 917833319414844733454563 := by
  unfold tailWord_1787474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16298633181573612275006369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43463021817529632733350317 16298633181573612275006369)
  ·
    refine ⟨12223974886180209206254777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16298633181573612275006369 12223974886180209206254777)
    ·
      refine ⟨9167981164635156904691083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12223974886180209206254777 9167981164635156904691083)
      ·
        refine ⟨13751971746952735357036625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9167981164635156904691083 13751971746952735357036625)
        ·
          refine ⟨10313978810214551517777469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13751971746952735357036625 10313978810214551517777469)
          ·
            refine ⟨3867742053830456819166551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10313978810214551517777469 3867742053830456819166551)
            ·
              refine ⟨5801613080745685228749827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867742053830456819166551 5801613080745685228749827)
              ·
                refine ⟨8702419621118527843124741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801613080745685228749827 8702419621118527843124741)
                ·
                  refine ⟨1631703678959723970585889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8702419621118527843124741 1631703678959723970585889)
                  ·
                    refine ⟨1223777759219792977939417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631703678959723970585889 1223777759219792977939417)
                    ·
                      refine ⟨917833319414844733454563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223777759219792977939417 917833319414844733454563)
                      ·
                        rfl

theorem cell23_1787474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_1787474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787474 prefixEnd_1787474 := by exact prefixLift 1787474
  have htrace : WordTrace (prefixWord ++ tailWord_1787474) baseStart_1787474 baseEnd_1787474 := by
    simpa [prefixWord, tailWord_1787474, baseEnd_1787474] using wordTrace_append hprefix tailTrace_1787474
  have hstable : (prefixWord ++ tailWord_1787474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787474).length < 2 ^ (prefixWord ++ tailWord_1787474).sum := by decide
  have hdescent : baseEnd_1787474 < baseStart_1787474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787491 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1787491 : Nat := 118140960795 + 1787491 * 2 ^ 59
def prefixEnd_1787491 : Nat := 4983230072969 + 3 ^ 40 * 1787491 * 2
def baseEnd_1787491 : Nat := 917842048585971166941985

theorem tailTrace_1787491 : CollatzResearch.WordTrace tailWord_1787491 prefixEnd_1787491 917842048585971166941985 := by
  unfold tailWord_1787491
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195152767232861003394327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43463435178155240668929551 65195152767232861003394327)
  ·
    refine ⟨97792729150849291505091491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65195152767232861003394327 97792729150849291505091491)
    ·
      refine ⟨146689093726273937257637237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97792729150849291505091491 146689093726273937257637237)
      ·
        refine ⟨13752102536838181617903491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146689093726273937257637237 13752102536838181617903491)
        ·
          refine ⟨20628153805257272426855237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13752102536838181617903491 20628153805257272426855237)
          ·
            refine ⟨3867778838485738580035357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20628153805257272426855237 3867778838485738580035357)
            ·
              refine ⟨1450417064432151967513259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3867778838485738580035357 1450417064432151967513259)
              ·
                refine ⟨2175625596648227951269889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450417064432151967513259 2175625596648227951269889)
                ·
                  refine ⟨1631719197486170963452417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2175625596648227951269889 1631719197486170963452417)
                  ·
                    refine ⟨1223789398114628222589313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631719197486170963452417 1223789398114628222589313)
                    ·
                      refine ⟨917842048585971166941985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223789398114628222589313 917842048585971166941985)
                      ·
                        rfl

theorem cell23_1787491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1787491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787491 prefixEnd_1787491 := by exact prefixLift 1787491
  have htrace : WordTrace (prefixWord ++ tailWord_1787491) baseStart_1787491 baseEnd_1787491 := by
    simpa [prefixWord, tailWord_1787491, baseEnd_1787491] using wordTrace_append hprefix tailTrace_1787491
  have hstable : (prefixWord ++ tailWord_1787491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787491).length < 2 ^ (prefixWord ++ tailWord_1787491).sum := by decide
  have hdescent : baseEnd_1787491 < baseStart_1787491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787503 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_1787503 : Nat := 118140960795 + 1787503 * 2 ^ 59
def prefixEnd_1787503 : Nat := 4983230072969 + 3 ^ 40 * 1787503 * 2
def baseEnd_1787503 : Nat := 917848210353825119991929

theorem tailTrace_1787503 : CollatzResearch.WordTrace tailWord_1787503 prefixEnd_1787503 917848210353825119991929 := by
  unfold tailWord_1787503
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195590443189387052831163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43463726962126258035220775 65195590443189387052831163)
  ·
    refine ⟨97793385664784080579246745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65195590443189387052831163 97793385664784080579246745)
    ·
      refine ⟨73345039248588060434435059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97793385664784080579246745 73345039248588060434435059)
      ·
        refine ⟨110017558872882090651652589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73345039248588060434435059 110017558872882090651652589)
        ·
          refine ⟨41256584577330783994369721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110017558872882090651652589 41256584577330783994369721)
          ·
            refine ⟨30942438432998087995777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41256584577330783994369721 30942438432998087995777291)
            ·
              refine ⟨46413657649497131993665937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30942438432998087995777291 46413657649497131993665937)
              ·
                refine ⟨34810243237122848995249453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46413657649497131993665937 34810243237122848995249453)
                ·
                  refine ⟨13053841213921068373218545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34810243237122848995249453 13053841213921068373218545)
                  ·
                    refine ⟨9790380910440801279913909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13053841213921068373218545 9790380910440801279913909)
                    ·
                      refine ⟨917848210353825119991929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9790380910440801279913909 917848210353825119991929)
                      ·
                        rfl

theorem cell23_1787503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_1787503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787503 prefixEnd_1787503 := by exact prefixLift 1787503
  have htrace : WordTrace (prefixWord ++ tailWord_1787503) baseStart_1787503 baseEnd_1787503 := by
    simpa [prefixWord, tailWord_1787503, baseEnd_1787503] using wordTrace_append hprefix tailTrace_1787503
  have hstable : (prefixWord ++ tailWord_1787503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787503).length < 2 ^ (prefixWord ++ tailWord_1787503).sum := by decide
  have hdescent : baseEnd_1787503 < baseStart_1787503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787567 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_1787567 : Nat := 118140960795 + 1787567 * 2 ^ 59
def prefixEnd_1787567 : Nat := 4983230072969 + 3 ^ 40 * 1787567 * 2
def baseEnd_1787567 : Nat := 917881073115712869591635

theorem tailTrace_1787567 : CollatzResearch.WordTrace tailWord_1787567 prefixEnd_1787567 917881073115712869591635 := by
  unfold tailWord_1787567
  simp only [CollatzResearch.WordTrace]
  refine ⟨65197924714957525983160955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43465283143305017322107303 65197924714957525983160955)
  ·
    refine ⟨97796887072436288974741433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65197924714957525983160955 97796887072436288974741433)
    ·
      refine ⟨73347665304327216731056075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97796887072436288974741433 73347665304327216731056075)
      ·
        refine ⟨110021497956490825096584113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73347665304327216731056075 110021497956490825096584113)
        ·
          refine ⟨82516123467368118822438085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110021497956490825096584113 82516123467368118822438085)
          ·
            refine ⟨15471773150131522279207141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82516123467368118822438085 15471773150131522279207141)
            ·
              refine ⟨2900957465649660427351339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15471773150131522279207141 2900957465649660427351339)
              ·
                refine ⟨4351436198474490641027009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900957465649660427351339 4351436198474490641027009)
                ·
                  refine ⟨3263577148855867980770257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351436198474490641027009 3263577148855867980770257)
                  ·
                    refine ⟨2447682861641900985577693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263577148855867980770257 2447682861641900985577693)
                    ·
                      refine ⟨917881073115712869591635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447682861641900985577693 917881073115712869591635)
                      ·
                        rfl

theorem cell23_1787567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_1787567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787567 prefixEnd_1787567 := by exact prefixLift 1787567
  have htrace : WordTrace (prefixWord ++ tailWord_1787567) baseStart_1787567 baseEnd_1787567 := by
    simpa [prefixWord, tailWord_1787567, baseEnd_1787567] using wordTrace_append hprefix tailTrace_1787567
  have hstable : (prefixWord ++ tailWord_1787567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787567).length < 2 ^ (prefixWord ++ tailWord_1787567).sum := by decide
  have hdescent : baseEnd_1787567 < baseStart_1787567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787607 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_1787607 : Nat := 118140960795 + 1787607 * 2 ^ 59
def prefixEnd_1787607 : Nat := 4983230072969 + 3 ^ 40 * 1787607 * 2
def baseEnd_1787607 : Nat := 917901612341892713091451

theorem tailTrace_1787607 : CollatzResearch.WordTrace tailWord_1787607 prefixEnd_1787607 917901612341892713091451 := by
  unfold tailWord_1787607
  simp only [CollatzResearch.WordTrace]
  refine ⟨65199383634812612814617075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43466255756541741876411383 65199383634812612814617075)
  ·
    refine ⟨97799075452218919221925613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65199383634812612814617075 97799075452218919221925613)
    ·
      refine ⟨36674653294582094708222105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97799075452218919221925613 36674653294582094708222105)
      ·
        refine ⟨27505989970936571031166579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36674653294582094708222105 27505989970936571031166579)
        ·
          refine ⟨41258984956404856546749869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27505989970936571031166579 41258984956404856546749869)
          ·
            refine ⟨15472119358651821205031201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41258984956404856546749869 15472119358651821205031201)
            ·
              refine ⟨11604089518988865903773401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15472119358651821205031201 11604089518988865903773401)
              ·
                refine ⟨8703067139241649427830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604089518988865903773401 8703067139241649427830051)
                ·
                  refine ⟨13054600708862474141745077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703067139241649427830051 13054600708862474141745077)
                  ·
                    refine ⟨1223868816455856950788601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13054600708862474141745077 1223868816455856950788601)
                    ·
                      refine ⟨917901612341892713091451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223868816455856950788601 917901612341892713091451)
                      ·
                        rfl

theorem cell23_1787607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_1787607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787607 prefixEnd_1787607 := by exact prefixLift 1787607
  have htrace : WordTrace (prefixWord ++ tailWord_1787607) baseStart_1787607 baseEnd_1787607 := by
    simpa [prefixWord, tailWord_1787607, baseEnd_1787607] using wordTrace_append hprefix tailTrace_1787607
  have hstable : (prefixWord ++ tailWord_1787607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787607).length < 2 ^ (prefixWord ++ tailWord_1787607).sum := by decide
  have hdescent : baseEnd_1787607 < baseStart_1787607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787624 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1787624 : Nat := 118140960795 + 1787624 * 2 ^ 59
def prefixEnd_1787624 : Nat := 4983230072969 + 3 ^ 40 * 1787624 * 2
def baseEnd_1787624 : Nat := 917910341513019146578873

theorem tailTrace_1787624 : CollatzResearch.WordTrace tailWord_1787624 prefixEnd_1787624 917910341513019146578873 := by
  unfold tailWord_1787624
  simp only [CollatzResearch.WordTrace]
  refine ⟨32600001837875512358992963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43466669117167349811990617 32600001837875512358992963)
  ·
    refine ⟨48900002756813268538489445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32600001837875512358992963 48900002756813268538489445)
    ·
      refine ⟨9168750516902487850966771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48900002756813268538489445 9168750516902487850966771)
      ·
        refine ⟨13753125775353731776450157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9168750516902487850966771 13753125775353731776450157)
        ·
          refine ⟨5157422165757649416168809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13753125775353731776450157 5157422165757649416168809)
          ·
            refine ⟨3868066624318237062126607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5157422165757649416168809 3868066624318237062126607)
            ·
              refine ⟨5802099936477355593189911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868066624318237062126607 5802099936477355593189911)
              ·
                refine ⟨8703149904716033389784867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802099936477355593189911 8703149904716033389784867)
                ·
                  refine ⟨13054724857074050084677301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703149904716033389784867 13054724857074050084677301)
                  ·
                    refine ⟨1223880455350692195438497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13054724857074050084677301 1223880455350692195438497)
                    ·
                      refine ⟨917910341513019146578873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223880455350692195438497 917910341513019146578873)
                      ·
                        rfl

theorem cell23_1787624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1787624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787624 prefixEnd_1787624 := by exact prefixLift 1787624
  have htrace : WordTrace (prefixWord ++ tailWord_1787624) baseStart_1787624 baseEnd_1787624 := by
    simpa [prefixWord, tailWord_1787624, baseEnd_1787624] using wordTrace_append hprefix tailTrace_1787624
  have hstable : (prefixWord ++ tailWord_1787624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787624).length < 2 ^ (prefixWord ++ tailWord_1787624).sum := by decide
  have hdescent : baseEnd_1787624 < baseStart_1787624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787631 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 1, 1, 3]
def baseStart_1787631 : Nat := 118140960795 + 1787631 * 2 ^ 59
def prefixEnd_1787631 : Nat := 4983230072969 + 3 ^ 40 * 1787631 * 2
def baseEnd_1787631 : Nat := 917913935877600619191341

theorem tailTrace_1787631 : CollatzResearch.WordTrace tailWord_1787631 prefixEnd_1787631 917913935877600619191341 := by
  unfold tailWord_1787631
  simp only [CollatzResearch.WordTrace]
  refine ⟨65200258986725664913490747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43466839324483776608993831 65200258986725664913490747)
  ·
    refine ⟨97800388480088497370236121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65200258986725664913490747 97800388480088497370236121)
    ·
      refine ⟨73350291360066373027677091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97800388480088497370236121 73350291360066373027677091)
      ·
        refine ⟨110025437040099559541515637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73350291360066373027677091 110025437040099559541515637)
        ·
          refine ⟨10314884722509333707017091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110025437040099559541515637 10314884722509333707017091)
          ·
            refine ⟨15472327083764000560525637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314884722509333707017091 15472327083764000560525637)
            ·
              refine ⟨2901061328205750105098557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15472327083764000560525637 2901061328205750105098557)
              ·
                refine ⟨1087897998077156289411959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2901061328205750105098557 1087897998077156289411959)
                ·
                  refine ⟨1631846997115734434117939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087897998077156289411959 1631846997115734434117939)
                  ·
                    refine ⟨2447770495673601651176909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631846997115734434117939 2447770495673601651176909)
                    ·
                      refine ⟨917913935877600619191341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447770495673601651176909 917913935877600619191341)
                      ·
                        rfl

theorem cell23_1787631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 1, 3].length) (baseStart_1787631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787631 prefixEnd_1787631 := by exact prefixLift 1787631
  have htrace : WordTrace (prefixWord ++ tailWord_1787631) baseStart_1787631 baseEnd_1787631 := by
    simpa [prefixWord, tailWord_1787631, baseEnd_1787631] using wordTrace_append hprefix tailTrace_1787631
  have hstable : (prefixWord ++ tailWord_1787631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787631).length < 2 ^ (prefixWord ++ tailWord_1787631).sum := by decide
  have hdescent : baseEnd_1787631 < baseStart_1787631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787671 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1787671 : Nat := 118140960795 + 1787671 * 2 ^ 59
def prefixEnd_1787671 : Nat := 4983230072969 + 3 ^ 40 * 1787671 * 2
def baseEnd_1787671 : Nat := 917934475103780462691157

theorem tailTrace_1787671 : CollatzResearch.WordTrace tailWord_1787671 prefixEnd_1787671 917934475103780462691157 := by
  unfold tailWord_1787671
  simp only [CollatzResearch.WordTrace]
  refine ⟨65201717906580751744946867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43467811937720501163297911 65201717906580751744946867)
  ·
    refine ⟨97802576859871127617420301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65201717906580751744946867 97802576859871127617420301)
    ·
      refine ⟨36675966322451672856532613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97802576859871127617420301 36675966322451672856532613)
      ·
        refine ⟨6876743685459688660599865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36675966322451672856532613 6876743685459688660599865)
        ·
          refine ⟨5157557764094766495449899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6876743685459688660599865 5157557764094766495449899)
          ·
            refine ⟨7736336646142149743174849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157557764094766495449899 7736336646142149743174849)
            ·
              refine ⟨5802252484606612307381137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7736336646142149743174849 5802252484606612307381137)
              ·
                refine ⟨4351689363454959230535853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802252484606612307381137 4351689363454959230535853)
                ·
                  refine ⟨1631883511295609711450945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4351689363454959230535853 1631883511295609711450945)
                  ·
                    refine ⟨1223912633471707283588209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631883511295609711450945 1223912633471707283588209)
                    ·
                      refine ⟨917934475103780462691157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223912633471707283588209 917934475103780462691157)
                      ·
                        rfl

theorem cell23_1787671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1787671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787671 prefixEnd_1787671 := by exact prefixLift 1787671
  have htrace : WordTrace (prefixWord ++ tailWord_1787671) baseStart_1787671 baseEnd_1787671 := by
    simpa [prefixWord, tailWord_1787671, baseEnd_1787671] using wordTrace_append hprefix tailTrace_1787671
  have hstable : (prefixWord ++ tailWord_1787671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787671).length < 2 ^ (prefixWord ++ tailWord_1787671).sum := by decide
  have hdescent : baseEnd_1787671 < baseStart_1787671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787674 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1787674 : Nat := 118140960795 + 1787674 * 2 ^ 59
def prefixEnd_1787674 : Nat := 4983230072969 + 3 ^ 40 * 1787674 * 2
def baseEnd_1787674 : Nat := 917936015545743950953643

theorem tailTrace_1787674 : CollatzResearch.WordTrace tailWord_1787674 prefixEnd_1787674 917936015545743950953643 := by
  unfold tailWord_1787674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300456831392470814326519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43467884883713255504870717 16300456831392470814326519)
  ·
    refine ⟨24450685247088706221489779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16300456831392470814326519 24450685247088706221489779)
    ·
      refine ⟨36676027870633059332234669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24450685247088706221489779 36676027870633059332234669)
      ·
        refine ⟨13753510451487397249588001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36676027870633059332234669 13753510451487397249588001)
        ·
          refine ⟨10315132838615547937191001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13753510451487397249588001 10315132838615547937191001)
          ·
            refine ⟨7736349628961660952893251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10315132838615547937191001 7736349628961660952893251)
            ·
              refine ⟨11604524443442491429339877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736349628961660952893251 11604524443442491429339877)
              ·
                refine ⟨2175848333145467143001227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11604524443442491429339877 2175848333145467143001227)
                ·
                  refine ⟨3263772499718200714501841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175848333145467143001227 3263772499718200714501841)
                  ·
                    refine ⟨2447829374788650535876381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263772499718200714501841 2447829374788650535876381)
                    ·
                      refine ⟨917936015545743950953643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447829374788650535876381 917936015545743950953643)
                      ·
                        rfl

theorem cell23_1787674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1787674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787674 prefixEnd_1787674 := by exact prefixLift 1787674
  have htrace : WordTrace (prefixWord ++ tailWord_1787674) baseStart_1787674 baseEnd_1787674 := by
    simpa [prefixWord, tailWord_1787674, baseEnd_1787674] using wordTrace_append hprefix tailTrace_1787674
  have hstable : (prefixWord ++ tailWord_1787674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787674).length < 2 ^ (prefixWord ++ tailWord_1787674).sum := by decide
  have hdescent : baseEnd_1787674 < baseStart_1787674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787694 : List Nat := [4, 1, 3, 2, 2, 2, 9]
def baseStart_1787694 : Nat := 118140960795 + 1787694 * 2 ^ 59
def prefixEnd_1787694 : Nat := 4983230072969 + 3 ^ 40 * 1787694 * 2
def baseEnd_1787694 : Nat := 11332670187146097193871

theorem tailTrace_1787694 : CollatzResearch.WordTrace tailWord_1787694 prefixEnd_1787694 11332670187146097193871 := by
  unfold tailWord_1787694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150319598187178334129267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43468371190331617782022757 8150319598187178334129267)
  ·
    refine ⟨12225479397280767501193901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150319598187178334129267 12225479397280767501193901)
    ·
      refine ⟨4584554773980287812947713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12225479397280767501193901 4584554773980287812947713)
      ·
        refine ⟨3438416080485215859710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4584554773980287812947713 3438416080485215859710785)
        ·
          refine ⟨2578812060363911894783089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3438416080485215859710785 2578812060363911894783089)
          ·
            refine ⟨1934109045272933921087317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2578812060363911894783089 1934109045272933921087317)
            ·
              refine ⟨11332670187146097193871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1934109045272933921087317 11332670187146097193871)
              ·
                rfl

theorem cell23_1787694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 9].length) (baseStart_1787694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787694 prefixEnd_1787694 := by exact prefixLift 1787694
  have htrace : WordTrace (prefixWord ++ tailWord_1787694) baseStart_1787694 baseEnd_1787694 := by
    simpa [prefixWord, tailWord_1787694, baseEnd_1787694] using wordTrace_append hprefix tailTrace_1787694
  have hstable : (prefixWord ++ tailWord_1787694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787694).length < 2 ^ (prefixWord ++ tailWord_1787694).sum := by decide
  have hdescent : baseEnd_1787694 < baseStart_1787694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787704 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_1787704 : Nat := 118140960795 + 1787704 * 2 ^ 59
def prefixEnd_1787704 : Nat := 4983230072969 + 3 ^ 40 * 1787704 * 2
def baseEnd_1787704 : Nat := 917951419965378833578505

theorem tailTrace_1787704 : CollatzResearch.WordTrace tailWord_1787704 prefixEnd_1787704 917951419965378833578505 := by
  unfold tailWord_1787704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601460757730599190449083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43468614343640798920598777 32601460757730599190449083)
  ·
    refine ⟨48902191136595898785673625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32601460757730599190449083 48902191136595898785673625)
    ·
      refine ⟨36676643352446924089255219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48902191136595898785673625 36676643352446924089255219)
      ·
        refine ⟨55014965028670386133882829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36676643352446924089255219 55014965028670386133882829)
        ·
          refine ⟨20630611885751394800206061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55014965028670386133882829 20630611885751394800206061)
          ·
            refine ⟨7736479457156773050077273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20630611885751394800206061 7736479457156773050077273)
            ·
              refine ⟨5802359592867579787557955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7736479457156773050077273 5802359592867579787557955)
              ·
                refine ⟨8703539389301369681336933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802359592867579787557955 8703539389301369681336933)
                ·
                  refine ⟨1631913635494006815250675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8703539389301369681336933 1631913635494006815250675)
                  ·
                    refine ⟨2447870453241010222876013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631913635494006815250675 2447870453241010222876013)
                    ·
                      refine ⟨917951419965378833578505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2447870453241010222876013 917951419965378833578505)
                      ·
                        rfl

theorem cell23_1787704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_1787704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787704 prefixEnd_1787704 := by exact prefixLift 1787704
  have htrace : WordTrace (prefixWord ++ tailWord_1787704) baseStart_1787704 baseEnd_1787704 := by
    simpa [prefixWord, tailWord_1787704, baseEnd_1787704] using wordTrace_append hprefix tailTrace_1787704
  have hstable : (prefixWord ++ tailWord_1787704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787704).length < 2 ^ (prefixWord ++ tailWord_1787704).sum := by decide
  have hdescent : baseEnd_1787704 < baseStart_1787704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787705 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1787705 : Nat := 118140960795 + 1787705 * 2 ^ 59
def prefixEnd_1787705 : Nat := 4983230072969 + 3 ^ 40 * 1787705 * 2
def baseEnd_1787705 : Nat := 917951933446033329666001

theorem tailTrace_1787705 : CollatzResearch.WordTrace tailWord_1787705 prefixEnd_1787705 917951933446033329666001 := by
  unfold tailWord_1787705
  simp only [CollatzResearch.WordTrace]
  refine ⟨65202957988457575551684569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43468638658971717034456379 65202957988457575551684569)
  ·
    refine ⟨48902218491343181663763427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65202957988457575551684569 48902218491343181663763427)
    ·
      refine ⟨73353327737014772495645141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48902218491343181663763427 73353327737014772495645141)
      ·
        refine ⟨1719218618836283730366683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73353327737014772495645141 1719218618836283730366683)
        ·
          refine ⟨2578827928254425595550025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719218618836283730366683 2578827928254425595550025)
          ·
            refine ⟨1934120946190819196662519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2578827928254425595550025 1934120946190819196662519)
            ·
              refine ⟨2901181419286228794993779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934120946190819196662519 2901181419286228794993779)
              ·
                refine ⟨4351772128929343192490669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901181419286228794993779 4351772128929343192490669)
                ·
                  refine ⟨1631914548348503697184001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4351772128929343192490669 1631914548348503697184001)
                  ·
                    refine ⟨1223935911261377772888001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631914548348503697184001 1223935911261377772888001)
                    ·
                      refine ⟨917951933446033329666001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223935911261377772888001 917951933446033329666001)
                      ·
                        rfl

theorem cell23_1787705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1787705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787705 prefixEnd_1787705 := by exact prefixLift 1787705
  have htrace : WordTrace (prefixWord ++ tailWord_1787705) baseStart_1787705 baseEnd_1787705 := by
    simpa [prefixWord, tailWord_1787705, baseEnd_1787705] using wordTrace_append hprefix tailTrace_1787705
  have hstable : (prefixWord ++ tailWord_1787705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787705).length < 2 ^ (prefixWord ++ tailWord_1787705).sum := by decide
  have hdescent : baseEnd_1787705 < baseStart_1787705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787744 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2]
def baseStart_1787744 : Nat := 118140960795 + 1787744 * 2 ^ 59
def prefixEnd_1787744 : Nat := 4983230072969 + 3 ^ 40 * 1787744 * 2
def baseEnd_1787744 : Nat := 917971959191558677078321

theorem tailTrace_1787744 : CollatzResearch.WordTrace tailWord_1787744 prefixEnd_1787744 917971959191558677078321 := by
  unfold tailWord_1787744
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602190217658142606177143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43469586956877523474902857 32602190217658142606177143)
  ·
    refine ⟨48903285326487213909265715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32602190217658142606177143 48903285326487213909265715)
    ·
      refine ⟨73354927989730820863898573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48903285326487213909265715 73354927989730820863898573)
      ·
        refine ⟨27508097996149057823961965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73354927989730820863898573 27508097996149057823961965)
        ·
          refine ⟨10315536748555896683985737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27508097996149057823961965 10315536748555896683985737)
          ·
            refine ⟨7736652561416922512989303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10315536748555896683985737 7736652561416922512989303)
            ·
              refine ⟨11604978842125383769483955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736652561416922512989303 11604978842125383769483955)
              ·
                refine ⟨17407468263188075654225933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604978842125383769483955 17407468263188075654225933)
                ·
                  refine ⟨6527800598695528370334725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17407468263188075654225933 6527800598695528370334725)
                  ·
                    refine ⟨1223962612255411569437761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527800598695528370334725 1223962612255411569437761)
                    ·
                      refine ⟨917971959191558677078321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223962612255411569437761 917971959191558677078321)
                      ·
                        rfl

theorem cell23_1787744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_1787744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787744 prefixEnd_1787744 := by exact prefixLift 1787744
  have htrace : WordTrace (prefixWord ++ tailWord_1787744) baseStart_1787744 baseEnd_1787744 := by
    simpa [prefixWord, tailWord_1787744, baseEnd_1787744] using wordTrace_append hprefix tailTrace_1787744
  have hstable : (prefixWord ++ tailWord_1787744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787744).length < 2 ^ (prefixWord ++ tailWord_1787744).sum := by decide
  have hdescent : baseEnd_1787744 < baseStart_1787744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787784 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 7]
def baseStart_1787784 : Nat := 118140960795 + 1787784 * 2 ^ 59
def prefixEnd_1787784 : Nat := 4983230072969 + 3 ^ 40 * 1787784 * 2
def baseEnd_1787784 : Nat := 101999166490859835619793

theorem tailTrace_1787784 : CollatzResearch.WordTrace tailWord_1787784 prefixEnd_1787784 101999166490859835619793 := by
  unfold tailWord_1787784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602919677585686021905203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43470559570114248029206937 32602919677585686021905203)
  ·
    refine ⟨48904379516378529032857805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32602919677585686021905203 48904379516378529032857805)
    ·
      refine ⟨18339142318641948387321677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48904379516378529032857805 18339142318641948387321677)
      ·
        refine ⟨6877178369490730645245629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18339142318641948387321677 6877178369490730645245629)
        ·
          refine ⟨2578941888559023991967111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6877178369490730645245629 2578941888559023991967111)
          ·
            refine ⟨3868412832838535987950667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578941888559023991967111 3868412832838535987950667)
            ·
              refine ⟨5802619249257803981926001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868412832838535987950667 5802619249257803981926001)
              ·
                refine ⟨4351964436943352986444501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802619249257803981926001 4351964436943352986444501)
                ·
                  refine ⟨101999166490859835619793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4351964436943352986444501 101999166490859835619793)
                  ·
                    rfl

theorem cell23_1787784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_1787784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787784 prefixEnd_1787784 := by exact prefixLift 1787784
  have htrace : WordTrace (prefixWord ++ tailWord_1787784) baseStart_1787784 baseEnd_1787784 := by
    simpa [prefixWord, tailWord_1787784, baseEnd_1787784] using wordTrace_append hprefix tailTrace_1787784
  have hstable : (prefixWord ++ tailWord_1787784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787784).length < 2 ^ (prefixWord ++ tailWord_1787784).sum := by decide
  have hdescent : baseEnd_1787784 < baseStart_1787784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787797 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1787797 : Nat := 118140960795 + 1787797 * 2 ^ 59
def prefixEnd_1787797 : Nat := 4983230072969 + 3 ^ 40 * 1787797 * 2
def baseEnd_1787797 : Nat := 305999724555415656571859

theorem tailTrace_1787797 : CollatzResearch.WordTrace tailWord_1787797 prefixEnd_1787797 305999724555415656571859 := by
  unfold tailWord_1787797
  simp only [CollatzResearch.WordTrace]
  refine ⟨65206313504124275264033645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43470875669416183509355763 65206313504124275264033645)
  ·
    refine ⟨24452367564046603224012617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65206313504124275264033645 24452367564046603224012617)
    ·
      refine ⟨18339275673034952418009463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24452367564046603224012617 18339275673034952418009463)
      ·
        refine ⟨27508913509552428627014195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18339275673034952418009463 27508913509552428627014195)
        ·
          refine ⟨41263370264328642940521293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27508913509552428627014195 41263370264328642940521293)
          ·
            refine ⟨15473763849123241102695485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41263370264328642940521293 15473763849123241102695485)
            ·
              refine ⟨5802661443421215413510807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15473763849123241102695485 5802661443421215413510807)
              ·
                refine ⟨8703992165131823120266211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802661443421215413510807 8703992165131823120266211)
                ·
                  refine ⟨13055988247697734680399317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703992165131823120266211 13055988247697734680399317)
                  ·
                    refine ⟨305999724555415656571859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13055988247697734680399317 305999724555415656571859)
                    ·
                      rfl

theorem cell23_1787797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1787797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787797 prefixEnd_1787797 := by exact prefixLift 1787797
  have htrace : WordTrace (prefixWord ++ tailWord_1787797) baseStart_1787797 baseEnd_1787797 := by
    simpa [prefixWord, tailWord_1787797, baseEnd_1787797] using wordTrace_append hprefix tailTrace_1787797
  have hstable : (prefixWord ++ tailWord_1787797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787797).length < 2 ^ (prefixWord ++ tailWord_1787797).sum := by decide
  have hdescent : baseEnd_1787797 < baseStart_1787797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787834 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_1787834 : Nat := 118140960795 + 1787834 * 2 ^ 59
def prefixEnd_1787834 : Nat := 4983230072969 + 3 ^ 40 * 1787834 * 2
def baseEnd_1787834 : Nat := 918018172450463324952907

theorem tailTrace_1787834 : CollatzResearch.WordTrace tailWord_1787834 prefixEnd_1787834 918018172450463324952907 := by
  unfold tailWord_1787834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301915751247557645782639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43471775336660153722087037 16301915751247557645782639)
  ·
    refine ⟨24452873626871336468673959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16301915751247557645782639 24452873626871336468673959)
    ·
      refine ⟨36679310440307004703010939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24452873626871336468673959 36679310440307004703010939)
      ·
        refine ⟨55018965660460507054516409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36679310440307004703010939 55018965660460507054516409)
        ·
          refine ⟨41264224245345380290887307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55018965660460507054516409 41264224245345380290887307)
          ·
            refine ⟨61896336368018070436330961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41264224245345380290887307 61896336368018070436330961)
            ·
              refine ⟨46422252276013552827248221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61896336368018070436330961 46422252276013552827248221)
              ·
                refine ⟨17408344603505082310218083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46422252276013552827248221 17408344603505082310218083)
                ·
                  refine ⟨26112516905257623465327125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17408344603505082310218083 26112516905257623465327125)
                  ·
                    refine ⟨1224024229933951099937209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26112516905257623465327125 1224024229933951099937209)
                    ·
                      refine ⟨918018172450463324952907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224024229933951099937209 918018172450463324952907)
                      ·
                        rfl

theorem cell23_1787834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_1787834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787834 prefixEnd_1787834 := by exact prefixLift 1787834
  have htrace : WordTrace (prefixWord ++ tailWord_1787834) baseStart_1787834 baseEnd_1787834 := by
    simpa [prefixWord, tailWord_1787834, baseEnd_1787834] using wordTrace_append hprefix tailTrace_1787834
  have hstable : (prefixWord ++ tailWord_1787834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787834).length < 2 ^ (prefixWord ++ tailWord_1787834).sum := by decide
  have hdescent : baseEnd_1787834 < baseStart_1787834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787847 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1787847 : Nat := 118140960795 + 1787847 * 2 ^ 59
def prefixEnd_1787847 : Nat := 4983230072969 + 3 ^ 40 * 1787847 * 2
def baseEnd_1787847 : Nat := 918024847698971774090347

theorem tailTrace_1787847 : CollatzResearch.WordTrace tailWord_1787847 prefixEnd_1787847 918024847698971774090347 := by
  unfold tailWord_1787847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65208137153943133803353795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43472091435962089202235863 65208137153943133803353795)
  ·
    refine ⟨97812205730914700705030693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65208137153943133803353795 97812205730914700705030693)
    ·
      refine ⟨18339788574546506382193255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97812205730914700705030693 18339788574546506382193255)
      ·
        refine ⟨27509682861819759573289883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18339788574546506382193255 27509682861819759573289883)
        ·
          refine ⟨41264524292729639359934825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27509682861819759573289883 41264524292729639359934825)
          ·
            refine ⟨30948393219547229519951119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41264524292729639359934825 30948393219547229519951119)
            ·
              refine ⟨46422589829320844279926679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30948393219547229519951119 46422589829320844279926679)
              ·
                refine ⟨69633884743981266419890019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46422589829320844279926679 69633884743981266419890019)
                ·
                  refine ⟨104450827115971899629835029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69633884743981266419890019 104450827115971899629835029)
                  ·
                    refine ⟨4896132521061182795148517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104450827115971899629835029 4896132521061182795148517)
                    ·
                      refine ⟨918024847698971774090347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4896132521061182795148517 918024847698971774090347)
                      ·
                        rfl

theorem cell23_1787847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1787847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787847 prefixEnd_1787847 := by exact prefixLift 1787847
  have htrace : WordTrace (prefixWord ++ tailWord_1787847) baseStart_1787847 baseEnd_1787847 := by
    simpa [prefixWord, tailWord_1787847, baseEnd_1787847] using wordTrace_append hprefix tailTrace_1787847
  have hstable : (prefixWord ++ tailWord_1787847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787847).length < 2 ^ (prefixWord ++ tailWord_1787847).sum := by decide
  have hdescent : baseEnd_1787847 < baseStart_1787847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787854 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1787854 : Nat := 118140960795 + 1787854 * 2 ^ 59
def prefixEnd_1787854 : Nat := 4983230072969 + 3 ^ 40 * 1787854 * 2
def baseEnd_1787854 : Nat := 918028442063553246702815

theorem tailTrace_1787854 : CollatzResearch.WordTrace tailWord_1787854 prefixEnd_1787854 918028442063553246702815 := by
  unfold tailWord_1787854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151049058114721749857327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43472261643278515999239077 8151049058114721749857327)
  ·
    refine ⟨12226573587172082624785991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8151049058114721749857327 12226573587172082624785991)
    ·
      refine ⟨18339860380758123937178987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12226573587172082624785991 18339860380758123937178987)
      ·
        refine ⟨27509790571137185905768481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18339860380758123937178987 27509790571137185905768481)
        ·
          refine ⟨20632342928352889429326361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27509790571137185905768481 20632342928352889429326361)
          ·
            refine ⟨15474257196264667071994771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20632342928352889429326361 15474257196264667071994771)
            ·
              refine ⟨23211385794397000607992157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15474257196264667071994771 23211385794397000607992157)
              ·
                refine ⟨8704269672898875227997059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23211385794397000607992157 8704269672898875227997059)
                ·
                  refine ⟨13056404509348312841995589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8704269672898875227997059 13056404509348312841995589)
                  ·
                    refine ⟨2448075845502808657874173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13056404509348312841995589 2448075845502808657874173)
                    ·
                      refine ⟨918028442063553246702815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448075845502808657874173 918028442063553246702815)
                      ·
                        rfl

theorem cell23_1787854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1787854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787854 prefixEnd_1787854 := by exact prefixLift 1787854
  have htrace : WordTrace (prefixWord ++ tailWord_1787854) baseStart_1787854 baseEnd_1787854 := by
    simpa [prefixWord, tailWord_1787854, baseEnd_1787854] using wordTrace_append hprefix tailTrace_1787854
  have hstable : (prefixWord ++ tailWord_1787854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787854).length < 2 ^ (prefixWord ++ tailWord_1787854).sum := by decide
  have hdescent : baseEnd_1787854 < baseStart_1787854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787871 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1787871 : Nat := 118140960795 + 1787871 * 2 ^ 59
def prefixEnd_1787871 : Nat := 4983230072969 + 3 ^ 40 * 1787871 * 2
def baseEnd_1787871 : Nat := 918037171234679680190237

theorem tailTrace_1787871 : CollatzResearch.WordTrace tailWord_1787871 prefixEnd_1787871 918037171234679680190237 := by
  unfold tailWord_1787871
  simp only [CollatzResearch.WordTrace]
  refine ⟨65209012505856185902227467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43472675003904123934818311 65209012505856185902227467)
  ·
    refine ⟨97813518758784278853341201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65209012505856185902227467 97813518758784278853341201)
    ·
      refine ⟨73360139069088209140005901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97813518758784278853341201 73360139069088209140005901)
      ·
        refine ⟨27510052150908078427502213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73360139069088209140005901 27510052150908078427502213)
        ·
          refine ⟨5158134778295264705156665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27510052150908078427502213 5158134778295264705156665)
          ·
            refine ⟨3868601083721448528867499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158134778295264705156665 3868601083721448528867499)
            ·
              refine ⟨5802901625582172793301249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868601083721448528867499 5802901625582172793301249)
              ·
                refine ⟨4352176219186629594975937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802901625582172793301249 4352176219186629594975937)
                ·
                  refine ⟨3264132164389972196231953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352176219186629594975937 3264132164389972196231953)
                  ·
                    refine ⟨2448099123292479147173965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264132164389972196231953 2448099123292479147173965)
                    ·
                      refine ⟨918037171234679680190237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448099123292479147173965 918037171234679680190237)
                      ·
                        rfl

theorem cell23_1787871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1787871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787871 prefixEnd_1787871 := by exact prefixLift 1787871
  have htrace : WordTrace (prefixWord ++ tailWord_1787871) baseStart_1787871 baseEnd_1787871 := by
    simpa [prefixWord, tailWord_1787871, baseEnd_1787871] using wordTrace_append hprefix tailTrace_1787871
  have hstable : (prefixWord ++ tailWord_1787871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787871).length < 2 ^ (prefixWord ++ tailWord_1787871).sum := by decide
  have hdescent : baseEnd_1787871 < baseStart_1787871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787901 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1787901 : Nat := 118140960795 + 1787901 * 2 ^ 59
def prefixEnd_1787901 : Nat := 4983230072969 + 3 ^ 40 * 1787901 * 2
def baseEnd_1787901 : Nat := 918052575654314562815099

theorem tailTrace_1787901 : CollatzResearch.WordTrace tailWord_1787901 prefixEnd_1787901 918052575654314562815099 := by
  unfold tailWord_1787901
  simp only [CollatzResearch.WordTrace]
  refine ⟨65210106695747501025819557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43473404463831667350546371 65210106695747501025819557)
  ·
    refine ⟨12226895005452656442341167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65210106695747501025819557 12226895005452656442341167)
    ·
      refine ⟨18340342508178984663511751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12226895005452656442341167 18340342508178984663511751)
      ·
        refine ⟨27510513762268476995267627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18340342508178984663511751 27510513762268476995267627)
        ·
          refine ⟨41265770643402715492901441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27510513762268476995267627 41265770643402715492901441)
          ·
            refine ⟨30949327982552036619676081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41265770643402715492901441 30949327982552036619676081)
            ·
              refine ⟨23211995986914027464757061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30949327982552036619676081 23211995986914027464757061)
              ·
                refine ⟨4352249247546380149641949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23211995986914027464757061 4352249247546380149641949)
                ·
                  refine ⟨1632093467829892556115731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4352249247546380149641949 1632093467829892556115731)
                  ·
                    refine ⟨2448140201744838834173597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632093467829892556115731 2448140201744838834173597)
                    ·
                      refine ⟨918052575654314562815099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448140201744838834173597 918052575654314562815099)
                      ·
                        rfl

theorem cell23_1787901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1787901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787901 prefixEnd_1787901 := by exact prefixLift 1787901
  have htrace : WordTrace (prefixWord ++ tailWord_1787901) baseStart_1787901 baseEnd_1787901 := by
    simpa [prefixWord, tailWord_1787901, baseEnd_1787901] using wordTrace_append hprefix tailTrace_1787901
  have hstable : (prefixWord ++ tailWord_1787901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787901).length < 2 ^ (prefixWord ++ tailWord_1787901).sum := by decide
  have hdescent : baseEnd_1787901 < baseStart_1787901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787904 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_1787904 : Nat := 118140960795 + 1787904 * 2 ^ 59
def prefixEnd_1787904 : Nat := 4983230072969 + 3 ^ 40 * 1787904 * 2
def baseEnd_1787904 : Nat := 306018038698759350359195

theorem tailTrace_1787904 : CollatzResearch.WordTrace tailWord_1787904 prefixEnd_1787904 306018038698759350359195 := by
  unfold tailWord_1787904
  simp only [CollatzResearch.WordTrace]
  refine ⟨32605108057368316269089383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43473477409824421692119177 32605108057368316269089383)
  ·
    refine ⟨48907662086052474403634075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32605108057368316269089383 48907662086052474403634075)
    ·
      refine ⟨73361493129078711605451113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48907662086052474403634075 73361493129078711605451113)
      ·
        refine ⟨55021119846809033704088335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73361493129078711605451113 55021119846809033704088335)
        ·
          refine ⟨82531679770213550556132503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55021119846809033704088335 82531679770213550556132503)
          ·
            refine ⟨123797519655320325834198755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82531679770213550556132503 123797519655320325834198755)
            ·
              refine ⟨185696279482980488751298133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123797519655320325834198755 185696279482980488751298133)
              ·
                refine ⟨2176128275191177602554275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 185696279482980488751298133 2176128275191177602554275)
                ·
                  refine ⟨3264192412786766403831413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176128275191177602554275 3264192412786766403831413)
                  ·
                    refine ⟨306018038698759350359195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3264192412786766403831413 306018038698759350359195)
                    ·
                      rfl

theorem cell23_1787904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_1787904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787904 prefixEnd_1787904 := by exact prefixLift 1787904
  have htrace : WordTrace (prefixWord ++ tailWord_1787904) baseStart_1787904 baseEnd_1787904 := by
    simpa [prefixWord, tailWord_1787904, baseEnd_1787904] using wordTrace_append hprefix tailTrace_1787904
  have hstable : (prefixWord ++ tailWord_1787904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787904).length < 2 ^ (prefixWord ++ tailWord_1787904).sum := by decide
  have hdescent : baseEnd_1787904 < baseStart_1787904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787947 : List Nat := [1, 1, 1, 1, 2, 1, 4, 12]
def baseStart_1787947 : Nat := 118140960795 + 1787947 * 2 ^ 59
def prefixEnd_1787947 : Nat := 4983230072969 + 3 ^ 40 * 1787947 * 2
def baseEnd_1787947 : Nat := 34002822065348940105181

theorem tailTrace_1787947 : CollatzResearch.WordTrace tailWord_1787947 prefixEnd_1787947 34002822065348940105181 := by
  unfold tailWord_1787947
  simp only [CollatzResearch.WordTrace]
  refine ⟨65211784453580850881994095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43474522969053900587996063 65211784453580850881994095)
  ·
    refine ⟨97817676680371276322991143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65211784453580850881994095 97817676680371276322991143)
    ·
      refine ⟨146726515020556914484486715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97817676680371276322991143 146726515020556914484486715)
      ·
        refine ⟨220089772530835371726730073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146726515020556914484486715 220089772530835371726730073)
        ·
          refine ⟨165067329398126528795047555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220089772530835371726730073 165067329398126528795047555)
          ·
            refine ⟨247600994097189793192571333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165067329398126528795047555 247600994097189793192571333)
            ·
              refine ⟨46425186393223086223607125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247600994097189793192571333 46425186393223086223607125)
              ·
                refine ⟨34002822065348940105181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 46425186393223086223607125 34002822065348940105181)
                ·
                  rfl

theorem cell23_1787947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 12].length) (baseStart_1787947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787947 prefixEnd_1787947 := by exact prefixLift 1787947
  have htrace : WordTrace (prefixWord ++ tailWord_1787947) baseStart_1787947 baseEnd_1787947 := by
    simpa [prefixWord, tailWord_1787947, baseEnd_1787947] using wordTrace_append hprefix tailTrace_1787947
  have hstable : (prefixWord ++ tailWord_1787947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787947).length < 2 ^ (prefixWord ++ tailWord_1787947).sum := by decide
  have hdescent : baseEnd_1787947 < baseStart_1787947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787958 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1787958 : Nat := 118140960795 + 1787958 * 2 ^ 59
def prefixEnd_1787958 : Nat := 4983230072969 + 3 ^ 40 * 1787958 * 2
def baseEnd_1787958 : Nat := 918081844051620839802337

theorem tailTrace_1787958 : CollatzResearch.WordTrace tailWord_1787958 prefixEnd_1787958 918081844051620839802337 := by
  unfold tailWord_1787958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075761603533812485040283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43474790437693999840429685 4075761603533812485040283)
  ·
    refine ⟨6113642405300718727560425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075761603533812485040283 6113642405300718727560425)
    ·
      refine ⟨4585231803975539045670319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6113642405300718727560425 4585231803975539045670319)
      ·
        refine ⟨6877847705963308568505479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585231803975539045670319 6877847705963308568505479)
        ·
          refine ⟨10316771558944962852758219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877847705963308568505479 10316771558944962852758219)
          ·
            refine ⟨15475157338417444279137329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316771558944962852758219 15475157338417444279137329)
            ·
              refine ⟨11606368003813083209352997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15475157338417444279137329 11606368003813083209352997)
              ·
                refine ⟨2176194000714953101753687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11606368003813083209352997 2176194000714953101753687)
                ·
                  refine ⟨3264291001072429652630531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176194000714953101753687 3264291001072429652630531)
                  ·
                    refine ⟨4896436501608644478945797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264291001072429652630531 4896436501608644478945797)
                    ·
                      refine ⟨918081844051620839802337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4896436501608644478945797 918081844051620839802337)
                      ·
                        rfl

theorem cell23_1787958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1787958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1787958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1787958 prefixEnd_1787958 := by exact prefixLift 1787958
  have htrace : WordTrace (prefixWord ++ tailWord_1787958) baseStart_1787958 baseEnd_1787958 := by
    simpa [prefixWord, tailWord_1787958, baseEnd_1787958] using wordTrace_append hprefix tailTrace_1787958
  have hstable : (prefixWord ++ tailWord_1787958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787958).length < 2 ^ (prefixWord ++ tailWord_1787958).sum := by decide
  have hdescent : baseEnd_1787958 < baseStart_1787958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788002 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1788002 : Nat := 118140960795 + 1788002 * 2 ^ 59
def prefixEnd_1788002 : Nat := 4983230072969 + 3 ^ 40 * 1788002 * 2
def baseEnd_1788002 : Nat := 306034812400139555884045

theorem tailTrace_1788002 : CollatzResearch.WordTrace tailWord_1788002 prefixEnd_1788002 306034812400139555884045 := by
  unfold tailWord_1788002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303447617095398818811565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43475860312254396850164173 16303447617095398818811565)
  ·
    refine ⟨6113792856410774557054337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16303447617095398818811565 6113792856410774557054337)
    ·
      refine ⟨4585344642308080917790753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6113792856410774557054337 4585344642308080917790753)
      ·
        refine ⟨3439008481731060688343065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585344642308080917790753 3439008481731060688343065)
        ·
          refine ⟨2579256361298295516257299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439008481731060688343065 2579256361298295516257299)
          ·
            refine ⟨3868884541947443274385949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579256361298295516257299 3868884541947443274385949)
            ·
              refine ⟨1450831703230291227894731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3868884541947443274385949 1450831703230291227894731)
              ·
                refine ⟨2176247554845436841842097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450831703230291227894731 2176247554845436841842097)
                ·
                  refine ⟨1632185666134077631381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176247554845436841842097 1632185666134077631381573)
                  ·
                    refine ⟨306034812400139555884045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632185666134077631381573 306034812400139555884045)
                    ·
                      rfl

theorem cell23_1788002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1788002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788002 prefixEnd_1788002 := by exact prefixLift 1788002
  have htrace : WordTrace (prefixWord ++ tailWord_1788002) baseStart_1788002 baseEnd_1788002 := by
    simpa [prefixWord, tailWord_1788002, baseEnd_1788002] using wordTrace_append hprefix tailTrace_1788002
  have hstable : (prefixWord ++ tailWord_1788002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788002).length < 2 ^ (prefixWord ++ tailWord_1788002).sum := by decide
  have hdescent : baseEnd_1788002 < baseStart_1788002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788048 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2]
def baseStart_1788048 : Nat := 118140960795 + 1788048 * 2 ^ 59
def prefixEnd_1788048 : Nat := 4983230072969 + 3 ^ 40 * 1788048 * 2
def baseEnd_1788048 : Nat := 918128057310525487676923

theorem tailTrace_1788048 : CollatzResearch.WordTrace tailWord_1788048 prefixEnd_1788048 918128057310525487676923 := by
  unfold tailWord_1788048
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607734113107472565710399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43476978817476630087613865 32607734113107472565710399)
  ·
    refine ⟨48911601169661208848565599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32607734113107472565710399 48911601169661208848565599)
    ·
      refine ⟨73367401754491813272848399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48911601169661208848565599 73367401754491813272848399)
      ·
        refine ⟨110051102631737719909272599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73367401754491813272848399 110051102631737719909272599)
        ·
          refine ⟨165076653947606579863908899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110051102631737719909272599 165076653947606579863908899)
          ·
            refine ⟨247614980921409869795863349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165076653947606579863908899 247614980921409869795863349)
            ·
              refine ⟨23213904461382175293362189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247614980921409869795863349 23213904461382175293362189)
              ·
                refine ⟨8705214173018315735010821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23213904461382175293362189 8705214173018315735010821)
                ·
                  refine ⟨1632227657440934200314529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8705214173018315735010821 1632227657440934200314529)
                  ·
                    refine ⟨1224170743080700650235897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632227657440934200314529 1224170743080700650235897)
                    ·
                      refine ⟨918128057310525487676923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224170743080700650235897 918128057310525487676923)
                      ·
                        rfl

theorem cell23_1788048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2].length) (baseStart_1788048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788048 prefixEnd_1788048 := by exact prefixLift 1788048
  have htrace : WordTrace (prefixWord ++ tailWord_1788048) baseStart_1788048 baseEnd_1788048 := by
    simpa [prefixWord, tailWord_1788048, baseEnd_1788048] using wordTrace_append hprefix tailTrace_1788048
  have hstable : (prefixWord ++ tailWord_1788048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788048).length < 2 ^ (prefixWord ++ tailWord_1788048).sum := by decide
  have hdescent : baseEnd_1788048 < baseStart_1788048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788101 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1788101 : Nat := 118140960795 + 1788101 * 2 ^ 59
def prefixEnd_1788101 : Nat := 4983230072969 + 3 ^ 40 * 1788101 * 2
def baseEnd_1788101 : Nat := 306051757261737926771393

theorem tailTrace_1788101 : CollatzResearch.WordTrace tailWord_1788101 prefixEnd_1788101 306051757261737926771393 := by
  unfold tailWord_1788101
  simp only [CollatzResearch.WordTrace]
  refine ⟨65217401295022935183100157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43478267530015290122066771 65217401295022935183100157)
  ·
    refine ⟨24456525485633600693662559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65217401295022935183100157 24456525485633600693662559)
    ·
      refine ⟨36684788228450401040493839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456525485633600693662559 36684788228450401040493839)
      ·
        refine ⟨55027182342675601560740759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36684788228450401040493839 55027182342675601560740759)
        ·
          refine ⟨82540773514013402341111139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55027182342675601560740759 82540773514013402341111139)
          ·
            refine ⟨123811160271020103511666709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82540773514013402341111139 123811160271020103511666709)
            ·
              refine ⟨5803648137704067352109377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123811160271020103511666709 5803648137704067352109377)
              ·
                refine ⟨4352736103278050514082033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803648137704067352109377 4352736103278050514082033)
                ·
                  refine ⟨3264552077458537885561525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352736103278050514082033 3264552077458537885561525)
                  ·
                    refine ⟨306051757261737926771393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3264552077458537885561525 306051757261737926771393)
                    ·
                      rfl

theorem cell23_1788101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1788101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788101 prefixEnd_1788101 := by exact prefixLift 1788101
  have htrace : WordTrace (prefixWord ++ tailWord_1788101) baseStart_1788101 baseEnd_1788101 := by
    simpa [prefixWord, tailWord_1788101, baseEnd_1788101] using wordTrace_append hprefix tailTrace_1788101
  have hstable : (prefixWord ++ tailWord_1788101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788101).length < 2 ^ (prefixWord ++ tailWord_1788101).sum := by decide
  have hdescent : baseEnd_1788101 < baseStart_1788101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788121 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1788121 : Nat := 118140960795 + 1788121 * 2 ^ 59
def prefixEnd_1788121 : Nat := 4983230072969 + 3 ^ 40 * 1788121 * 2
def baseEnd_1788121 : Nat := 918165541398303702064087

theorem tailTrace_1788121 : CollatzResearch.WordTrace tailWord_1788121 prefixEnd_1788121 918165541398303702064087 := by
  unfold tailWord_1788121
  simp only [CollatzResearch.WordTrace]
  refine ⟨65218130754950478598828217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43478753836633652399218811 65218130754950478598828217)
  ·
    refine ⟨48913598066212858949121163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65218130754950478598828217 48913598066212858949121163)
    ·
      refine ⟨73370397099319288423681745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48913598066212858949121163 73370397099319288423681745)
      ·
        refine ⟨55027797824489466317761309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73370397099319288423681745 55027797824489466317761309)
        ·
          refine ⟨20635424184183549869160491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55027797824489466317761309 20635424184183549869160491)
          ·
            refine ⟨30953136276275324803740737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20635424184183549869160491 30953136276275324803740737)
            ·
              refine ⟨23214852207206493602805553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30953136276275324803740737 23214852207206493602805553)
              ·
                refine ⟨17411139155404870202104165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23214852207206493602805553 17411139155404870202104165)
                ·
                  refine ⟨3264588591638413162894531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17411139155404870202104165 3264588591638413162894531)
                  ·
                    refine ⟨4896882887457619744341797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264588591638413162894531 4896882887457619744341797)
                    ·
                      refine ⟨918165541398303702064087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4896882887457619744341797 918165541398303702064087)
                      ·
                        rfl

theorem cell23_1788121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1788121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788121 prefixEnd_1788121 := by exact prefixLift 1788121
  have htrace : WordTrace (prefixWord ++ tailWord_1788121) baseStart_1788121 baseEnd_1788121 := by
    simpa [prefixWord, tailWord_1788121, baseEnd_1788121] using wordTrace_append hprefix tailTrace_1788121
  have hstable : (prefixWord ++ tailWord_1788121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788121).length < 2 ^ (prefixWord ++ tailWord_1788121).sum := by decide
  have hdescent : baseEnd_1788121 < baseStart_1788121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788135 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1788135 : Nat := 118140960795 + 1788135 * 2 ^ 59
def prefixEnd_1788135 : Nat := 4983230072969 + 3 ^ 40 * 1788135 * 2
def baseEnd_1788135 : Nat := 306057576709155549096341

theorem tailTrace_1788135 : CollatzResearch.WordTrace tailWord_1788135 prefixEnd_1788135 306057576709155549096341 := by
  unfold tailWord_1788135
  simp only [CollatzResearch.WordTrace]
  refine ⟨65218641376899758989837859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43479094251266505993225239 65218641376899758989837859)
  ·
    refine ⟨97827962065349638484756789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65218641376899758989837859 97827962065349638484756789)
    ·
      refine ⟨9171371443626528607945949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97827962065349638484756789 9171371443626528607945949)
      ·
        refine ⟨3439264291359948227979731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9171371443626528607945949 3439264291359948227979731)
        ·
          refine ⟨5158896437039922341969597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439264291359948227979731 5158896437039922341969597)
          ·
            refine ⟨1934586163889970878238599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5158896437039922341969597 1934586163889970878238599)
            ·
              refine ⟨2901879245834956317357899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934586163889970878238599 2901879245834956317357899)
              ·
                refine ⟨4352818868752434476036849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901879245834956317357899 4352818868752434476036849)
                ·
                  refine ⟨3264614151564325857027637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352818868752434476036849 3264614151564325857027637)
                  ·
                    refine ⟨306057576709155549096341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3264614151564325857027637 306057576709155549096341)
                    ·
                      rfl

theorem cell23_1788135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1788135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788135 prefixEnd_1788135 := by exact prefixLift 1788135
  have htrace : WordTrace (prefixWord ++ tailWord_1788135) baseStart_1788135 baseEnd_1788135 := by
    simpa [prefixWord, tailWord_1788135, baseEnd_1788135] using wordTrace_append hprefix tailTrace_1788135
  have hstable : (prefixWord ++ tailWord_1788135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788135).length < 2 ^ (prefixWord ++ tailWord_1788135).sum := by decide
  have hdescent : baseEnd_1788135 < baseStart_1788135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788138 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_1788138 : Nat := 118140960795 + 1788138 * 2 ^ 59
def prefixEnd_1788138 : Nat := 4983230072969 + 3 ^ 40 * 1788138 * 2
def baseEnd_1788138 : Nat := 918174270569430135551509

theorem tailTrace_1788138 : CollatzResearch.WordTrace tailWord_1788138 prefixEnd_1788138 918174270569430135551509 := by
  unfold tailWord_1788138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304687698972222625549267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43479167197259260334798045 16304687698972222625549267)
  ·
    refine ⟨24457031548458333938323901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16304687698972222625549267 24457031548458333938323901)
    ·
      refine ⟨9171386830671875226871463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24457031548458333938323901 9171386830671875226871463)
      ·
        refine ⟨13757080246007812840307195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9171386830671875226871463 13757080246007812840307195)
        ·
          refine ⟨20635620369011719260460793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757080246007812840307195 20635620369011719260460793)
          ·
            refine ⟨15476715276758789445345595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20635620369011719260460793 15476715276758789445345595)
            ·
              refine ⟨23215072915138184168018393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15476715276758789445345595 23215072915138184168018393)
              ·
                refine ⟨17411304686353638126013795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23215072915138184168018393 17411304686353638126013795)
                ·
                  refine ⟨26116957029530457189020693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17411304686353638126013795 26116957029530457189020693)
                  ·
                    refine ⟨1224232360759240180735345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26116957029530457189020693 1224232360759240180735345)
                    ·
                      refine ⟨918174270569430135551509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224232360759240180735345 918174270569430135551509)
                      ·
                        rfl

theorem cell23_1788138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_1788138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788138 prefixEnd_1788138 := by exact prefixLift 1788138
  have htrace : WordTrace (prefixWord ++ tailWord_1788138) baseStart_1788138 baseEnd_1788138 := by
    simpa [prefixWord, tailWord_1788138, baseEnd_1788138] using wordTrace_append hprefix tailTrace_1788138
  have hstable : (prefixWord ++ tailWord_1788138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788138).length < 2 ^ (prefixWord ++ tailWord_1788138).sum := by decide
  have hdescent : baseEnd_1788138 < baseStart_1788138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788161 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 8]
def baseStart_1788161 : Nat := 118140960795 + 1788161 * 2 ^ 59
def prefixEnd_1788161 : Nat := 4983230072969 + 3 ^ 40 * 1788161 * 2
def baseEnd_1788161 : Nat := 102020675624942616173767

theorem tailTrace_1788161 : CollatzResearch.WordTrace tailWord_1788161 prefixEnd_1788161 102020675624942616173767 := by
  unfold tailWord_1788161
  simp only [CollatzResearch.WordTrace]
  refine ⟨65219589674805565430284337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43479726449870376953522891 65219589674805565430284337)
  ·
    refine ⟨48914692256104174072713253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65219589674805565430284337 48914692256104174072713253)
    ·
      refine ⟨9171504798019532638633735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48914692256104174072713253 9171504798019532638633735)
      ·
        refine ⟨13757257197029298957950603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9171504798019532638633735 13757257197029298957950603)
        ·
          refine ⟨20635885795543948436925905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757257197029298957950603 20635885795543948436925905)
          ·
            refine ⟨15476914346657961327694429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20635885795543948436925905 15476914346657961327694429)
            ·
              refine ⟨5803842879996735497885411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15476914346657961327694429 5803842879996735497885411)
              ·
                refine ⟨8705764319995103246828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803842879996735497885411 8705764319995103246828117)
                ·
                  refine ⟨102020675624942616173767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8705764319995103246828117 102020675624942616173767)
                  ·
                    rfl

theorem cell23_1788161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_1788161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788161 prefixEnd_1788161 := by exact prefixLift 1788161
  have htrace : WordTrace (prefixWord ++ tailWord_1788161) baseStart_1788161 baseEnd_1788161 := by
    simpa [prefixWord, tailWord_1788161, baseEnd_1788161] using wordTrace_append hprefix tailTrace_1788161
  have hstable : (prefixWord ++ tailWord_1788161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788161).length < 2 ^ (prefixWord ++ tailWord_1788161).sum := by decide
  have hdescent : baseEnd_1788161 < baseStart_1788161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788222 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1788222 : Nat := 118140960795 + 1788222 * 2 ^ 59
def prefixEnd_1788222 : Nat := 4983230072969 + 3 ^ 40 * 1788222 * 2
def baseEnd_1788222 : Nat := 918217402944407806901123

theorem tailTrace_1788222 : CollatzResearch.WordTrace tailWord_1788222 prefixEnd_1788222 918217402944407806901123 := by
  unfold tailWord_1788222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152726815948071606031865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43481209685056381898836613 8152726815948071606031865)
  ·
    refine ⟨6114545111961053704523899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8152726815948071606031865 6114545111961053704523899)
    ·
      refine ⟨9171817667941580556785849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6114545111961053704523899 9171817667941580556785849)
      ·
        refine ⟨6878863250956185417589387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9171817667941580556785849 6878863250956185417589387)
        ·
          refine ⟨10318294876434278126384081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878863250956185417589387 10318294876434278126384081)
          ·
            refine ⟨7738721157325708594788061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10318294876434278126384081 7738721157325708594788061)
            ·
              refine ⟨2902020433997140723045523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7738721157325708594788061 2902020433997140723045523)
              ·
                refine ⟨4353030650995711084568285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902020433997140723045523 4353030650995711084568285)
                ·
                  refine ⟨1632386494123391656713107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4353030650995711084568285 1632386494123391656713107)
                  ·
                    refine ⟨2448579741185087485069661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632386494123391656713107 2448579741185087485069661)
                    ·
                      refine ⟨918217402944407806901123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448579741185087485069661 918217402944407806901123)
                      ·
                        rfl

theorem cell23_1788222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1788222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788222 prefixEnd_1788222 := by exact prefixLift 1788222
  have htrace : WordTrace (prefixWord ++ tailWord_1788222) baseStart_1788222 baseEnd_1788222 := by
    simpa [prefixWord, tailWord_1788222, baseEnd_1788222] using wordTrace_append hprefix tailTrace_1788222
  have hstable : (prefixWord ++ tailWord_1788222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788222).length < 2 ^ (prefixWord ++ tailWord_1788222).sum := by decide
  have hdescent : baseEnd_1788222 < baseStart_1788222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788238 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1788238 : Nat := 118140960795 + 1788238 * 2 ^ 59
def prefixEnd_1788238 : Nat := 4983230072969 + 3 ^ 40 * 1788238 * 2
def baseEnd_1788238 : Nat := 306075206211626581433683

theorem tailTrace_1788238 : CollatzResearch.WordTrace tailWord_1788238 prefixEnd_1788238 306075206211626581433683 := by
  unfold tailWord_1788238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152799761940825947604671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43481598730351071720558245 8152799761940825947604671)
  ·
    refine ⟨12229199642911238921407007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8152799761940825947604671 12229199642911238921407007)
    ·
      refine ⟨18343799464366858382110511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12229199642911238921407007 18343799464366858382110511)
      ·
        refine ⟨27515699196550287573165767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343799464366858382110511 27515699196550287573165767)
        ·
          refine ⟨41273548794825431359748651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515699196550287573165767 41273548794825431359748651)
          ·
            refine ⟨61910323192238147039622977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41273548794825431359748651 61910323192238147039622977)
            ·
              refine ⟨46432742394178610279717233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61910323192238147039622977 46432742394178610279717233)
              ·
                refine ⟨34824556795633957709787925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46432742394178610279717233 34824556795633957709787925)
                ·
                  refine ⟨1632401099795341767646309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34824556795633957709787925 1632401099795341767646309)
                  ·
                    refine ⟨306075206211626581433683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632401099795341767646309 306075206211626581433683)
                    ·
                      rfl

theorem cell23_1788238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1788238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788238 prefixEnd_1788238 := by exact prefixLift 1788238
  have htrace : WordTrace (prefixWord ++ tailWord_1788238) baseStart_1788238 baseEnd_1788238 := by
    simpa [prefixWord, tailWord_1788238, baseEnd_1788238] using wordTrace_append hprefix tailTrace_1788238
  have hstable : (prefixWord ++ tailWord_1788238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788238).length < 2 ^ (prefixWord ++ tailWord_1788238).sum := by decide
  have hdescent : baseEnd_1788238 < baseStart_1788238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788245 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1788245 : Nat := 118140960795 + 1788245 * 2 ^ 59
def prefixEnd_1788245 : Nat := 4983230072969 + 3 ^ 40 * 1788245 * 2
def baseEnd_1788245 : Nat := 918229212999461216913517

theorem tailTrace_1788245 : CollatzResearch.WordTrace tailWord_1788245 prefixEnd_1788245 918229212999461216913517 := by
  unfold tailWord_1788245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65222653406501247776342189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43481768937667498517561459 65222653406501247776342189)
  ·
    refine ⟨24458495027437967916128321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65222653406501247776342189 24458495027437967916128321)
    ·
      refine ⟨18343871270578475937096241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24458495027437967916128321 18343871270578475937096241)
      ·
        refine ⟨13757903452933856952822181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18343871270578475937096241 13757903452933856952822181)
        ·
          refine ⟨2579606897425098178654159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13757903452933856952822181 2579606897425098178654159)
          ·
            refine ⟨3869410346137647267981239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579606897425098178654159 3869410346137647267981239)
            ·
              refine ⟨5804115519206470901971859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869410346137647267981239 5804115519206470901971859)
              ·
                refine ⟨8706173278809706352957789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804115519206470901971859 8706173278809706352957789)
                ·
                  refine ⟨3264814979553639882359171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8706173278809706352957789 3264814979553639882359171)
                  ·
                    refine ⟨4897222469330459823538757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264814979553639882359171 4897222469330459823538757)
                    ·
                      refine ⟨918229212999461216913517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4897222469330459823538757 918229212999461216913517)
                      ·
                        rfl

theorem cell23_1788245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1788245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788245 prefixEnd_1788245 := by exact prefixLift 1788245
  have htrace : WordTrace (prefixWord ++ tailWord_1788245) baseStart_1788245 baseEnd_1788245 := by
    simpa [prefixWord, tailWord_1788245, baseEnd_1788245] using wordTrace_append hprefix tailTrace_1788245
  have hstable : (prefixWord ++ tailWord_1788245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788245).length < 2 ^ (prefixWord ++ tailWord_1788245).sum := by decide
  have hdescent : baseEnd_1788245 < baseStart_1788245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788268 : List Nat := [2, 2, 1, 1, 7, 10]
def baseStart_1788268 : Nat := 118140960795 + 1788268 * 2 ^ 59
def prefixEnd_1788268 : Nat := 4983230072969 + 3 ^ 40 * 1788268 * 2
def baseEnd_1788268 : Nat := 3778769642199648670477

theorem tailTrace_1788268 : CollatzResearch.WordTrace tailWord_1788268 prefixEnd_1788268 3778769642199648670477 := by
  unfold tailWord_1788268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32611746142708961352214729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43482328190278615136286305 32611746142708961352214729)
  ·
    refine ⟨24458809607031721014161047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32611746142708961352214729 24458809607031721014161047)
    ·
      refine ⟨36688214410547581521241571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24458809607031721014161047 36688214410547581521241571)
      ·
        refine ⟨55032321615821372281862357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36688214410547581521241571 55032321615821372281862357)
        ·
          refine ⟨1289820037870813412856149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55032321615821372281862357 1289820037870813412856149)
          ·
            refine ⟨3778769642199648670477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1289820037870813412856149 3778769642199648670477)
            ·
              rfl

theorem cell23_1788268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 10].length) (baseStart_1788268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788268 prefixEnd_1788268 := by exact prefixLift 1788268
  have htrace : WordTrace (prefixWord ++ tailWord_1788268) baseStart_1788268 baseEnd_1788268 := by
    simpa [prefixWord, tailWord_1788268, baseEnd_1788268] using wordTrace_append hprefix tailTrace_1788268
  have hstable : (prefixWord ++ tailWord_1788268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788268).length < 2 ^ (prefixWord ++ tailWord_1788268).sum := by decide
  have hdescent : baseEnd_1788268 < baseStart_1788268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_1788271 : Nat := 118140960795 + 1788271 * 2 ^ 59
def prefixEnd_1788271 : Nat := 4983230072969 + 3 ^ 40 * 1788271 * 2
def baseEnd_1788271 : Nat := 918242563496478115188397

theorem tailTrace_1788271 : CollatzResearch.WordTrace tailWord_1788271 prefixEnd_1788271 918242563496478115188397 := by
  unfold tailWord_1788271
  simp only [CollatzResearch.WordTrace]
  refine ⟨65223601704407054216788667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43482401136271369477859111 65223601704407054216788667)
  ·
    refine ⟨97835402556610581325183001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65223601704407054216788667 97835402556610581325183001)
    ·
      refine ⟨73376551917457935993887251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97835402556610581325183001 73376551917457935993887251)
      ·
        refine ⟨110064827876186903990830877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73376551917457935993887251 110064827876186903990830877)
        ·
          refine ⟨41274310453570088996561579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110064827876186903990830877 41274310453570088996561579)
          ·
            refine ⟨61911465680355133494842369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41274310453570088996561579 61911465680355133494842369)
            ·
              refine ⟨46433599260266350121131777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61911465680355133494842369 46433599260266350121131777)
              ·
                refine ⟨34825199445199762590848833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46433599260266350121131777 34825199445199762590848833)
                ·
                  refine ⟨26118899583899821943136625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34825199445199762590848833 26118899583899821943136625)
                  ·
                    refine ⟨19589174687924866457352469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26118899583899821943136625 19589174687924866457352469)
                    ·
                      refine ⟨918242563496478115188397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19589174687924866457352469 918242563496478115188397)
                      ·
                        rfl

theorem cell23_1788271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_1788271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788271 prefixEnd_1788271 := by exact prefixLift 1788271
  have htrace : WordTrace (prefixWord ++ tailWord_1788271) baseStart_1788271 baseEnd_1788271 := by
    simpa [prefixWord, tailWord_1788271, baseEnd_1788271] using wordTrace_append hprefix tailTrace_1788271
  have hstable : (prefixWord ++ tailWord_1788271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788271).length < 2 ^ (prefixWord ++ tailWord_1788271).sum := by decide
  have hdescent : baseEnd_1788271 < baseStart_1788271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788295 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1788295 : Nat := 118140960795 + 1788295 * 2 ^ 59
def prefixEnd_1788295 : Nat := 4983230072969 + 3 ^ 40 * 1788295 * 2
def baseEnd_1788295 : Nat := 918254887032186021288287

theorem tailTrace_1788295 : CollatzResearch.WordTrace tailWord_1788295 prefixEnd_1788295 918254887032186021288287 := by
  unfold tailWord_1788295
  simp only [CollatzResearch.WordTrace]
  refine ⟨65224477056320106315662339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43482984704213404210441559 65224477056320106315662339)
  ·
    refine ⟨97836715584480159473493509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65224477056320106315662339 97836715584480159473493509)
    ·
      refine ⟨18344384172090029901280033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97836715584480159473493509 18344384172090029901280033)
      ·
        refine ⟨13758288129067522425960025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18344384172090029901280033 13758288129067522425960025)
        ·
          refine ⟨10318716096800641819470019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13758288129067522425960025 10318716096800641819470019)
          ·
            refine ⟨15478074145200962729205029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318716096800641819470019 15478074145200962729205029)
            ·
              refine ⟨2902138902225180511725943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15478074145200962729205029 2902138902225180511725943)
              ·
                refine ⟨4353208353337770767588915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902138902225180511725943 4353208353337770767588915)
                ·
                  refine ⟨6529812530006656151383373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353208353337770767588915 6529812530006656151383373)
                  ·
                    refine ⟨2448679698752496056768765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6529812530006656151383373 2448679698752496056768765)
                    ·
                      refine ⟨918254887032186021288287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448679698752496056768765 918254887032186021288287)
                      ·
                        rfl

theorem cell23_1788295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1788295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788295 prefixEnd_1788295 := by exact prefixLift 1788295
  have htrace : WordTrace (prefixWord ++ tailWord_1788295) baseStart_1788295 baseEnd_1788295 := by
    simpa [prefixWord, tailWord_1788295, baseEnd_1788295] using wordTrace_append hprefix tailTrace_1788295
  have hstable : (prefixWord ++ tailWord_1788295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788295).length < 2 ^ (prefixWord ++ tailWord_1788295).sum := by decide
  have hdescent : baseEnd_1788295 < baseStart_1788295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788310 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1788310 : Nat := 118140960795 + 1788310 * 2 ^ 59
def prefixEnd_1788310 : Nat := 4983230072969 + 3 ^ 40 * 1788310 * 2
def baseEnd_1788310 : Nat := 306087529747334487533573

theorem tailTrace_1788310 : CollatzResearch.WordTrace tailWord_1788310 prefixEnd_1788310 306087529747334487533573 := by
  unfold tailWord_1788310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076564009454110242341149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43483349434177175918305589 4076564009454110242341149)
  ·
    refine ⟨1528711503545291340877931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4076564009454110242341149 1528711503545291340877931)
    ·
      refine ⟨2293067255317937011316897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528711503545291340877931 2293067255317937011316897)
      ·
        refine ⟨1719800441488452758487673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2293067255317937011316897 1719800441488452758487673)
        ·
          refine ⟨1289850331116339568865755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719800441488452758487673 1289850331116339568865755)
          ·
            refine ⟨1934775496674509353298633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289850331116339568865755 1934775496674509353298633)
            ·
              refine ⟨1451081622505882014973975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934775496674509353298633 1451081622505882014973975)
              ·
                refine ⟨2176622433758823022460963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451081622505882014973975 2176622433758823022460963)
                ·
                  refine ⟨3264933650638234533691445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176622433758823022460963 3264933650638234533691445)
                  ·
                    refine ⟨306087529747334487533573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3264933650638234533691445 306087529747334487533573)
                    ·
                      rfl

theorem cell23_1788310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1788310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788310 prefixEnd_1788310 := by exact prefixLift 1788310
  have htrace : WordTrace (prefixWord ++ tailWord_1788310) baseStart_1788310 baseEnd_1788310 := by
    simpa [prefixWord, tailWord_1788310, baseEnd_1788310] using wordTrace_append hprefix tailTrace_1788310
  have hstable : (prefixWord ++ tailWord_1788310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788310).length < 2 ^ (prefixWord ++ tailWord_1788310).sum := by decide
  have hdescent : baseEnd_1788310 < baseStart_1788310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788356 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1788356 : Nat := 118140960795 + 1788356 * 2 ^ 59
def prefixEnd_1788356 : Nat := 4983230072969 + 3 ^ 40 * 1788356 * 2
def baseEnd_1788356 : Nat := 918286209352110282625507

theorem tailTrace_1788356 : CollatzResearch.WordTrace tailWord_1788356 prefixEnd_1788356 918286209352110282625507 := by
  unfold tailWord_1788356
  simp only [CollatzResearch.WordTrace]
  refine ⟨32613350954549556866816461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43484467939399409155755281 32613350954549556866816461)
  ·
    refine ⟨12230006607956083825056173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32613350954549556866816461 12230006607956083825056173)
    ·
      refine ⟨4586252477983531434396065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12230006607956083825056173 4586252477983531434396065)
      ·
        refine ⟨3439689358487648575797049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4586252477983531434396065 3439689358487648575797049)
        ·
          refine ⟨2579767018865736431847787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439689358487648575797049 2579767018865736431847787)
          ·
            refine ⟨3869650528298604647771681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579767018865736431847787 3869650528298604647771681)
            ·
              refine ⟨2902237896223953485828761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869650528298604647771681 2902237896223953485828761)
              ·
                refine ⟨2176678422167965114371571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902237896223953485828761 2176678422167965114371571)
                ·
                  refine ⟨3265017633251947671557357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176678422167965114371571 3265017633251947671557357)
                  ·
                    refine ⟨1224381612469480376834009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265017633251947671557357 1224381612469480376834009)
                    ·
                      refine ⟨918286209352110282625507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224381612469480376834009 918286209352110282625507)
                      ·
                        rfl

theorem cell23_1788356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1788356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788356 prefixEnd_1788356 := by exact prefixLift 1788356
  have htrace : WordTrace (prefixWord ++ tailWord_1788356) baseStart_1788356 baseEnd_1788356 := by
    simpa [prefixWord, tailWord_1788356, baseEnd_1788356] using wordTrace_append hprefix tailTrace_1788356
  have hstable : (prefixWord ++ tailWord_1788356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788356).length < 2 ^ (prefixWord ++ tailWord_1788356).sum := by decide
  have hdescent : baseEnd_1788356 < baseStart_1788356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788395 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 5, 2]
def baseStart_1788395 : Nat := 118140960795 + 1788395 * 2 ^ 59
def prefixEnd_1788395 : Nat := 4983230072969 + 3 ^ 40 * 1788395 * 2
def baseEnd_1788395 : Nat := 918306235097635630037827

theorem tailTrace_1788395 : CollatzResearch.WordTrace tailWord_1788395 prefixEnd_1788395 918306235097635630037827 := by
  unfold tailWord_1788395
  simp only [CollatzResearch.WordTrace]
  refine ⟨65228124355957823394302639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43485416237305215596201759 65228124355957823394302639)
  ·
    refine ⟨97842186533936735091453959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65228124355957823394302639 97842186533936735091453959)
    ·
      refine ⟨146763279800905102637180939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97842186533936735091453959 146763279800905102637180939)
      ·
        refine ⟨220144919701357653955771409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146763279800905102637180939 220144919701357653955771409)
        ·
          refine ⟨165108689776018240466828557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220144919701357653955771409 165108689776018240466828557)
          ·
            refine ⟨61915758666006840175060709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165108689776018240466828557 61915758666006840175060709)
            ·
              refine ⟨11609204749876282532823883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61915758666006840175060709 11609204749876282532823883)
              ·
                refine ⟨17413807124814423799235825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609204749876282532823883 17413807124814423799235825)
                ·
                  refine ⟨13060355343610817849426869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17413807124814423799235825 13060355343610817849426869)
                  ·
                    refine ⟨1224408313463514173383769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13060355343610817849426869 1224408313463514173383769)
                    ·
                      refine ⟨918306235097635630037827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224408313463514173383769 918306235097635630037827)
                      ·
                        rfl

theorem cell23_1788395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5, 2].length) (baseStart_1788395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788395 prefixEnd_1788395 := by exact prefixLift 1788395
  have htrace : WordTrace (prefixWord ++ tailWord_1788395) baseStart_1788395 baseEnd_1788395 := by
    simpa [prefixWord, tailWord_1788395, baseEnd_1788395] using wordTrace_append hprefix tailTrace_1788395
  have hstable : (prefixWord ++ tailWord_1788395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788395).length < 2 ^ (prefixWord ++ tailWord_1788395).sum := by decide
  have hdescent : baseEnd_1788395 < baseStart_1788395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788425 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 6, 2]
def baseStart_1788425 : Nat := 118140960795 + 1788425 * 2 ^ 59
def prefixEnd_1788425 : Nat := 4983230072969 + 3 ^ 40 * 1788425 * 2
def baseEnd_1788425 : Nat := 918321639517270512662689

theorem tailTrace_1788425 : CollatzResearch.WordTrace tailWord_1788425 prefixEnd_1788425 918321639517270512662689 := by
  unfold tailWord_1788425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65229218545849138517894729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43486145697232759011929819 65229218545849138517894729)
  ·
    refine ⟨48921913909386853888421047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65229218545849138517894729 48921913909386853888421047)
    ·
      refine ⟨73382870864080280832631571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48921913909386853888421047 73382870864080280832631571)
      ·
        refine ⟨110074306296120421248947357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73382870864080280832631571 110074306296120421248947357)
        ·
          refine ⟨41277864861045157968355259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110074306296120421248947357 41277864861045157968355259)
          ·
            refine ⟨61916797291567736952532889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41277864861045157968355259 61916797291567736952532889)
            ·
              refine ⟨46437597968675802714399667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61916797291567736952532889 46437597968675802714399667)
              ·
                refine ⟨69656396953013704071599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46437597968675802714399667 69656396953013704071599501)
                ·
                  refine ⟨26121148857380139026849813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69656396953013704071599501 26121148857380139026849813)
                  ·
                    refine ⟨1224428852689694016883585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26121148857380139026849813 1224428852689694016883585)
                    ·
                      refine ⟨918321639517270512662689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224428852689694016883585 918321639517270512662689)
                      ·
                        rfl

theorem cell23_1788425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6, 2].length) (baseStart_1788425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788425 prefixEnd_1788425 := by exact prefixLift 1788425
  have htrace : WordTrace (prefixWord ++ tailWord_1788425) baseStart_1788425 baseEnd_1788425 := by
    simpa [prefixWord, tailWord_1788425, baseEnd_1788425] using wordTrace_append hprefix tailTrace_1788425
  have hstable : (prefixWord ++ tailWord_1788425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788425).length < 2 ^ (prefixWord ++ tailWord_1788425).sum := by decide
  have hdescent : baseEnd_1788425 < baseStart_1788425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788465 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 6]
def baseStart_1788465 : Nat := 118140960795 + 1788465 * 2 ^ 59
def prefixEnd_1788465 : Nat := 4983230072969 + 3 ^ 40 * 1788465 * 2
def baseEnd_1788465 : Nat := 102038019860383372906945

theorem tailTrace_1788465 : CollatzResearch.WordTrace tailWord_1788465 prefixEnd_1788465 102038019860383372906945 := by
  unfold tailWord_1788465
  simp only [CollatzResearch.WordTrace]
  refine ⟨65230677465704225349350849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43487118310469483566233899 65230677465704225349350849)
  ·
    refine ⟨48923008099278169012013137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65230677465704225349350849 48923008099278169012013137)
    ·
      refine ⟨36692256074458626759009853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48923008099278169012013137 36692256074458626759009853)
      ·
        refine ⟨13759596027921985034628695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36692256074458626759009853 13759596027921985034628695)
        ·
          refine ⟨20639394041882977551943043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759596027921985034628695 20639394041882977551943043)
          ·
            refine ⟨30959091062824466327914565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20639394041882977551943043 30959091062824466327914565)
            ·
              refine ⟨5804829574279587436483981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30959091062824466327914565 5804829574279587436483981)
              ·
                refine ⟨2176811090354845288681493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5804829574279587436483981 2176811090354845288681493)
                ·
                  refine ⟨102038019860383372906945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2176811090354845288681493 102038019860383372906945)
                  ·
                    rfl

theorem cell23_1788465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_1788465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788465 prefixEnd_1788465 := by exact prefixLift 1788465
  have htrace : WordTrace (prefixWord ++ tailWord_1788465) baseStart_1788465 baseEnd_1788465 := by
    simpa [prefixWord, tailWord_1788465, baseEnd_1788465] using wordTrace_append hprefix tailTrace_1788465
  have hstable : (prefixWord ++ tailWord_1788465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788465).length < 2 ^ (prefixWord ++ tailWord_1788465).sum := by decide
  have hdescent : baseEnd_1788465 < baseStart_1788465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788492 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1788492 : Nat := 118140960795 + 1788492 * 2 ^ 59
def prefixEnd_1788492 : Nat := 4983230072969 + 3 ^ 40 * 1788492 * 2
def baseEnd_1788492 : Nat := 918356042721121750524881

theorem tailTrace_1788492 : CollatzResearch.WordTrace tailWord_1788492 prefixEnd_1788492 918356042721121750524881 := by
  unfold tailWord_1788492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615831118303204480291865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43487774824404272640389153 32615831118303204480291865)
  ·
    refine ⟨24461873338727403360218899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32615831118303204480291865 24461873338727403360218899)
    ·
      refine ⟨36692810008091105040328349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24461873338727403360218899 36692810008091105040328349)
      ·
        refine ⟨13759803753034164390123131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36692810008091105040328349 13759803753034164390123131)
        ·
          refine ⟨20639705629551246585184697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759803753034164390123131 20639705629551246585184697)
          ·
            refine ⟨15479779222163434938888523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639705629551246585184697 15479779222163434938888523)
            ·
              refine ⟨23219668833245152408332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15479779222163434938888523 23219668833245152408332785)
              ·
                refine ⟨17414751624933864306249589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23219668833245152408332785 17414751624933864306249589)
                ·
                  refine ⟨1632632964837549778710899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17414751624933864306249589 1632632964837549778710899)
                  ·
                    refine ⟨2448949447256324668066349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632632964837549778710899 2448949447256324668066349)
                    ·
                      refine ⟨918356042721121750524881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2448949447256324668066349 918356042721121750524881)
                      ·
                        rfl

theorem cell23_1788492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1788492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788492 prefixEnd_1788492 := by exact prefixLift 1788492
  have htrace : WordTrace (prefixWord ++ tailWord_1788492) baseStart_1788492 baseEnd_1788492 := by
    simpa [prefixWord, tailWord_1788492, baseEnd_1788492] using wordTrace_append hprefix tailTrace_1788492
  have hstable : (prefixWord ++ tailWord_1788492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788492).length < 2 ^ (prefixWord ++ tailWord_1788492).sum := by decide
  have hdescent : baseEnd_1788492 < baseStart_1788492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788562 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1788562 : Nat := 118140960795 + 1788562 * 2 ^ 59
def prefixEnd_1788562 : Nat := 4983230072969 + 3 ^ 40 * 1788562 * 2
def baseEnd_1788562 : Nat := 918391986366936476649559

theorem tailTrace_1788562 : CollatzResearch.WordTrace tailWord_1788562 prefixEnd_1788562 918391986366936476649559 := by
  unfold tailWord_1788562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308553836588202728907985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43489476897568540610421293 16308553836588202728907985)
  ·
    refine ⟨12231415377441152046680989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16308553836588202728907985 12231415377441152046680989)
    ·
      refine ⟨4586780766540432017505371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12231415377441152046680989 4586780766540432017505371)
      ·
        refine ⟨6880171149810648026258057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586780766540432017505371 6880171149810648026258057)
        ·
          refine ⟨5160128362357986019693543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6880171149810648026258057 5160128362357986019693543)
          ·
            refine ⟨7740192543536979029540315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160128362357986019693543 7740192543536979029540315)
            ·
              refine ⟨11610288815305468544310473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740192543536979029540315 11610288815305468544310473)
              ·
                refine ⟨8707716611479101408232855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11610288815305468544310473 8707716611479101408232855)
                ·
                  refine ⟨13061574917218652112349283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707716611479101408232855 13061574917218652112349283)
                  ·
                    refine ⟨19592362375827978168523925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13061574917218652112349283 19592362375827978168523925)
                    ·
                      refine ⟨918391986366936476649559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19592362375827978168523925 918391986366936476649559)
                      ·
                        rfl

theorem cell23_1788562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1788562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788562 prefixEnd_1788562 := by exact prefixLift 1788562
  have htrace : WordTrace (prefixWord ++ tailWord_1788562) baseStart_1788562 baseEnd_1788562 := by
    simpa [prefixWord, tailWord_1788562, baseEnd_1788562] using wordTrace_append hprefix tailTrace_1788562
  have hstable : (prefixWord ++ tailWord_1788562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788562).length < 2 ^ (prefixWord ++ tailWord_1788562).sum := by decide
  have hdescent : baseEnd_1788562 < baseStart_1788562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788572 : List Nat := [2, 2, 3, 2, 2, 2, 2, 8]
def baseStart_1788572 : Nat := 118140960795 + 1788572 * 2 ^ 59
def prefixEnd_1788572 : Nat := 4983230072969 + 3 ^ 40 * 1788572 * 2
def baseEnd_1788572 : Nat := 34014708191610423612019

theorem tailTrace_1788572 : CollatzResearch.WordTrace tailWord_1788572 prefixEnd_1788572 34014708191610423612019 := by
  unfold tailWord_1788572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617290038158291311747985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43489720050877721748997313 32617290038158291311747985)
  ·
    refine ⟨24462967528618718483810989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32617290038158291311747985 24462967528618718483810989)
    ·
      refine ⟨9173612823232019431429121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24462967528618718483810989 9173612823232019431429121)
      ·
        refine ⟨6880209617424014573571841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9173612823232019431429121 6880209617424014573571841)
        ·
          refine ⟨5160157213068010930178881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6880209617424014573571841 5160157213068010930178881)
          ·
            refine ⟨3870117909801008197634161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160157213068010930178881 3870117909801008197634161)
            ·
              refine ⟨2902588432350756148225621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870117909801008197634161 2902588432350756148225621)
              ·
                refine ⟨34014708191610423612019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2902588432350756148225621 34014708191610423612019)
                ·
                  rfl

theorem cell23_1788572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 8].length) (baseStart_1788572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788572 prefixEnd_1788572 := by exact prefixLift 1788572
  have htrace : WordTrace (prefixWord ++ tailWord_1788572) baseStart_1788572 baseEnd_1788572 := by
    simpa [prefixWord, tailWord_1788572, baseEnd_1788572] using wordTrace_append hprefix tailTrace_1788572
  have hstable : (prefixWord ++ tailWord_1788572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788572).length < 2 ^ (prefixWord ++ tailWord_1788572).sum := by decide
  have hdescent : baseEnd_1788572 < baseStart_1788572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788583 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1788583 : Nat := 118140960795 + 1788583 * 2 ^ 59
def prefixEnd_1788583 : Nat := 4983230072969 + 3 ^ 40 * 1788583 * 2
def baseEnd_1788583 : Nat := 918402769460680894486963

theorem tailTrace_1788583 : CollatzResearch.WordTrace tailWord_1788583 prefixEnd_1788583 918402769460680894486963 := by
  unfold tailWord_1788583
  simp only [CollatzResearch.WordTrace]
  refine ⟨65234981279276731502146403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43489987519517821001430935 65234981279276731502146403)
  ·
    refine ⟨97852471918915097253219605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65234981279276731502146403 97852471918915097253219605)
    ·
      refine ⟨4586834621199145183744669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97852471918915097253219605 4586834621199145183744669)
      ·
        refine ⟨1720062982949679443904251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4586834621199145183744669 1720062982949679443904251)
        ·
          refine ⟨2580094474424519165856377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720062982949679443904251 2580094474424519165856377)
          ·
            refine ⟨1935070855818389374392283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580094474424519165856377 1935070855818389374392283)
            ·
              refine ⟨2902606283727584061588425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935070855818389374392283 2902606283727584061588425)
              ·
                refine ⟨2176954712795688046191319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902606283727584061588425 2176954712795688046191319)
                ·
                  refine ⟨3265432069193532069286979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176954712795688046191319 3265432069193532069286979)
                  ·
                    refine ⟨4898148103790298103930469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3265432069193532069286979 4898148103790298103930469)
                    ·
                      refine ⟨918402769460680894486963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4898148103790298103930469 918402769460680894486963)
                      ·
                        rfl

theorem cell23_1788583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1788583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788583 prefixEnd_1788583 := by exact prefixLift 1788583
  have htrace : WordTrace (prefixWord ++ tailWord_1788583) baseStart_1788583 baseEnd_1788583 := by
    simpa [prefixWord, tailWord_1788583, baseEnd_1788583] using wordTrace_append hprefix tailTrace_1788583
  have hstable : (prefixWord ++ tailWord_1788583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788583).length < 2 ^ (prefixWord ++ tailWord_1788583).sum := by decide
  have hdescent : baseEnd_1788583 < baseStart_1788583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788599 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1788599 : Nat := 118140960795 + 1788599 * 2 ^ 59
def prefixEnd_1788599 : Nat := 4983230072969 + 3 ^ 40 * 1788599 * 2
def baseEnd_1788599 : Nat := 918410985151152831886889

theorem tailTrace_1788599 : CollatzResearch.WordTrace tailWord_1788599 prefixEnd_1788599 918410985151152831886889 := by
  unfold tailWord_1788599
  simp only [CollatzResearch.WordTrace]
  refine ⟨65235564847218766234728851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43490376564812510823152567 65235564847218766234728851)
  ·
    refine ⟨97853347270828149352093277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65235564847218766234728851 97853347270828149352093277)
    ·
      refine ⟨36695005226560556007034979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97853347270828149352093277 36695005226560556007034979)
      ·
        refine ⟨55042507839840834010552469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36695005226560556007034979 55042507839840834010552469)
        ·
          refine ⟨2580117554992539094244647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55042507839840834010552469 2580117554992539094244647)
          ·
            refine ⟨3870176332488808641366971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580117554992539094244647 3870176332488808641366971)
            ·
              refine ⟨5805264498733212962050457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870176332488808641366971 5805264498733212962050457)
              ·
                refine ⟨4353948374049909721537843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805264498733212962050457 4353948374049909721537843)
                ·
                  refine ⟨6530922561074864582306765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353948374049909721537843 6530922561074864582306765)
                  ·
                    refine ⟨2449095960403074218365037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6530922561074864582306765 2449095960403074218365037)
                    ·
                      refine ⟨918410985151152831886889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449095960403074218365037 918410985151152831886889)
                      ·
                        rfl

theorem cell23_1788599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1788599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788599 prefixEnd_1788599 := by exact prefixLift 1788599
  have htrace : WordTrace (prefixWord ++ tailWord_1788599) baseStart_1788599 baseEnd_1788599 := by
    simpa [prefixWord, tailWord_1788599, baseEnd_1788599] using wordTrace_append hprefix tailTrace_1788599
  have hstable : (prefixWord ++ tailWord_1788599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788599).length < 2 ^ (prefixWord ++ tailWord_1788599).sum := by decide
  have hdescent : baseEnd_1788599 < baseStart_1788599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788616 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1788616 : Nat := 118140960795 + 1788616 * 2 ^ 59
def prefixEnd_1788616 : Nat := 4983230072969 + 3 ^ 40 * 1788616 * 2
def baseEnd_1788616 : Nat := 918419714322279265374311

theorem tailTrace_1788616 : CollatzResearch.WordTrace tailWord_1788616 prefixEnd_1788616 918419714322279265374311 := by
  unfold tailWord_1788616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618092444078589069048851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43490789925438118758731801 32618092444078589069048851)
  ·
    refine ⟨48927138666117883603573277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32618092444078589069048851 48927138666117883603573277)
    ·
      refine ⟨18347676999794206351339979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48927138666117883603573277 18347676999794206351339979)
      ·
        refine ⟨27521515499691309527009969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347676999794206351339979 27521515499691309527009969)
        ·
          refine ⟨20641136624768482145257477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27521515499691309527009969 20641136624768482145257477)
          ·
            refine ⟨3870213117144090402235777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20641136624768482145257477 3870213117144090402235777)
            ·
              refine ⟨2902659837858067801676833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870213117144090402235777 2902659837858067801676833)
              ·
                refine ⟨2176994878393550851257625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902659837858067801676833 2176994878393550851257625)
                ·
                  refine ⟨1632746158795163138443219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176994878393550851257625 1632746158795163138443219)
                  ·
                    refine ⟨2449119238192744707664829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632746158795163138443219 2449119238192744707664829)
                    ·
                      refine ⟨918419714322279265374311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449119238192744707664829 918419714322279265374311)
                      ·
                        rfl

theorem cell23_1788616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1788616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788616 prefixEnd_1788616 := by exact prefixLift 1788616
  have htrace : WordTrace (prefixWord ++ tailWord_1788616) baseStart_1788616 baseEnd_1788616 := by
    simpa [prefixWord, tailWord_1788616, baseEnd_1788616] using wordTrace_append hprefix tailTrace_1788616
  have hstable : (prefixWord ++ tailWord_1788616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788616).length < 2 ^ (prefixWord ++ tailWord_1788616).sum := by decide
  have hdescent : baseEnd_1788616 < baseStart_1788616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788622 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1788622 : Nat := 118140960795 + 1788622 * 2 ^ 59
def prefixEnd_1788622 : Nat := 4983230072969 + 3 ^ 40 * 1788622 * 2
def baseEnd_1788622 : Nat := 918422795206206241899283

theorem tailTrace_1788622 : CollatzResearch.WordTrace tailWord_1788622 prefixEnd_1788622 918422795206206241899283 := by
  unfold tailWord_1788622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8154550465766930145352015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43490935817423627441877413 8154550465766930145352015)
  ·
    refine ⟨12231825698650395218028023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8154550465766930145352015 12231825698650395218028023)
    ·
      refine ⟨18347738547975592827042035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231825698650395218028023 18347738547975592827042035)
      ·
        refine ⟨27521607821963389240563053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347738547975592827042035 27521607821963389240563053)
        ·
          refine ⟨10320602933236270965211145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27521607821963389240563053 10320602933236270965211145)
          ·
            refine ⟨7740452199927203223908359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10320602933236270965211145 7740452199927203223908359)
            ·
              refine ⟨11610678299890804835862539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740452199927203223908359 11610678299890804835862539)
              ·
                refine ⟨17416017449836207253793809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610678299890804835862539 17416017449836207253793809)
                ·
                  refine ⟨13062013087377155440345357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17416017449836207253793809 13062013087377155440345357)
                  ·
                    refine ⟨4898254907766433290129509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13062013087377155440345357 4898254907766433290129509)
                    ·
                      refine ⟨918422795206206241899283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4898254907766433290129509 918422795206206241899283)
                      ·
                        rfl

theorem cell23_1788622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1788622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788622 prefixEnd_1788622 := by exact prefixLift 1788622
  have htrace : WordTrace (prefixWord ++ tailWord_1788622) baseStart_1788622 baseEnd_1788622 := by
    simpa [prefixWord, tailWord_1788622, baseEnd_1788622] using wordTrace_append hprefix tailTrace_1788622
  have hstable : (prefixWord ++ tailWord_1788622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788622).length < 2 ^ (prefixWord ++ tailWord_1788622).sum := by decide
  have hdescent : baseEnd_1788622 < baseStart_1788622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788632 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1788632 : Nat := 118140960795 + 1788632 * 2 ^ 59
def prefixEnd_1788632 : Nat := 4983230072969 + 3 ^ 40 * 1788632 * 2
def baseEnd_1788632 : Nat := 306142643337583734258079

theorem tailTrace_1788632 : CollatzResearch.WordTrace tailWord_1788632 prefixEnd_1788632 306142643337583734258079 := by
  unfold tailWord_1788632
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618384228049606435340075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43491178970732808580453433 32618384228049606435340075)
  ·
    refine ⟨48927576342074409653010113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32618384228049606435340075 48927576342074409653010113)
    ·
      refine ⟨36695682256555807239757585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48927576342074409653010113 36695682256555807239757585)
      ·
        refine ⟨27521761692416855429818189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36695682256555807239757585 27521761692416855429818189)
        ·
          refine ⟨10320660634656320786181821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27521761692416855429818189 10320660634656320786181821)
          ·
            refine ⟨3870247737996120294818183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10320660634656320786181821 3870247737996120294818183)
            ·
              refine ⟨5805371606994180442227275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870247737996120294818183 5805371606994180442227275)
              ·
                refine ⟨8708057410491270663340913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805371606994180442227275 8708057410491270663340913)
                ·
                  refine ⟨6531043057868452997505685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708057410491270663340913 6531043057868452997505685)
                  ·
                    refine ⟨306142643337583734258079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6531043057868452997505685 306142643337583734258079)
                    ·
                      rfl

theorem cell23_1788632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1788632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788632 prefixEnd_1788632 := by exact prefixLift 1788632
  have htrace : WordTrace (prefixWord ++ tailWord_1788632) baseStart_1788632 baseEnd_1788632 := by
    simpa [prefixWord, tailWord_1788632, baseEnd_1788632] using wordTrace_append hprefix tailTrace_1788632
  have hstable : (prefixWord ++ tailWord_1788632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788632).length < 2 ^ (prefixWord ++ tailWord_1788632).sum := by decide
  have hdescent : baseEnd_1788632 < baseStart_1788632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788639 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 4, 2]
def baseStart_1788639 : Nat := 118140960795 + 1788639 * 2 ^ 59
def prefixEnd_1788639 : Nat := 4983230072969 + 3 ^ 40 * 1788639 * 2
def baseEnd_1788639 : Nat := 918431524377332675386705

theorem tailTrace_1788639 : CollatzResearch.WordTrace tailWord_1788639 prefixEnd_1788639 918431524377332675386705 := by
  unfold tailWord_1788639
  simp only [CollatzResearch.WordTrace]
  refine ⟨65237023767073853066184971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43491349178049235377456647 65237023767073853066184971)
  ·
    refine ⟨97855535650610779599277457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65237023767073853066184971 97855535650610779599277457)
    ·
      refine ⟨73391651737958084699458093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97855535650610779599277457 73391651737958084699458093)
      ·
        refine ⟨27521869401734281762296785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73391651737958084699458093 27521869401734281762296785)
        ·
          refine ⟨20641402051300711321722589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27521869401734281762296785 20641402051300711321722589)
          ·
            refine ⟨7740525769237766745645971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20641402051300711321722589 7740525769237766745645971)
            ·
              refine ⟨11610788653856650118468957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740525769237766745645971 11610788653856650118468957)
              ·
                refine ⟨4354045745196243794425859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11610788653856650118468957 4354045745196243794425859)
                ·
                  refine ⟨6531068617794365691638789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354045745196243794425859 6531068617794365691638789)
                  ·
                    refine ⟨1224575365836443567182273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531068617794365691638789 1224575365836443567182273)
                    ·
                      refine ⟨918431524377332675386705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224575365836443567182273 918431524377332675386705)
                      ·
                        rfl

theorem cell23_1788639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_1788639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788639 prefixEnd_1788639 := by exact prefixLift 1788639
  have htrace : WordTrace (prefixWord ++ tailWord_1788639) baseStart_1788639 baseEnd_1788639 := by
    simpa [prefixWord, tailWord_1788639, baseEnd_1788639] using wordTrace_append hprefix tailTrace_1788639
  have hstable : (prefixWord ++ tailWord_1788639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788639).length < 2 ^ (prefixWord ++ tailWord_1788639).sum := by decide
  have hdescent : baseEnd_1788639 < baseStart_1788639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788662 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1788662 : Nat := 118140960795 + 1788662 * 2 ^ 59
def prefixEnd_1788662 : Nat := 4983230072969 + 3 ^ 40 * 1788662 * 2
def baseEnd_1788662 : Nat := 102049259381376231711011

theorem tailTrace_1788662 : CollatzResearch.WordTrace tailWord_1788662 prefixEnd_1788662 102049259381376231711011 := by
  unfold tailWord_1788662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077366415374407999642015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43491908430660351996181493 4077366415374407999642015)
  ·
    refine ⟨6116049623061611999463023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077366415374407999642015 6116049623061611999463023)
    ·
      refine ⟨9174074434592417999194535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116049623061611999463023 9174074434592417999194535)
      ·
        refine ⟨13761111651888626998791803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174074434592417999194535 13761111651888626998791803)
        ·
          refine ⟨20641667477832940498187705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761111651888626998791803 20641667477832940498187705)
          ·
            refine ⟨15481250608374705373640779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20641667477832940498187705 15481250608374705373640779)
            ·
              refine ⟨23221875912562058060461169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15481250608374705373640779 23221875912562058060461169)
              ·
                refine ⟨17416406934421543545345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23221875912562058060461169 17416406934421543545345877)
                ·
                  refine ⟨102049259381376231711011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17416406934421543545345877 102049259381376231711011)
                  ·
                    rfl

theorem cell23_1788662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1788662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788662 prefixEnd_1788662 := by exact prefixLift 1788662
  have htrace : WordTrace (prefixWord ++ tailWord_1788662) baseStart_1788662 baseEnd_1788662 := by
    simpa [prefixWord, tailWord_1788662, baseEnd_1788662] using wordTrace_append hprefix tailTrace_1788662
  have hstable : (prefixWord ++ tailWord_1788662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788662).length < 2 ^ (prefixWord ++ tailWord_1788662).sum := by decide
  have hdescent : baseEnd_1788662 < baseStart_1788662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788679 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 7]
def baseStart_1788679 : Nat := 118140960795 + 1788679 * 2 ^ 59
def prefixEnd_1788679 : Nat := 4983230072969 + 3 ^ 40 * 1788679 * 2
def baseEnd_1788679 : Nat := 102050229289279168765169

theorem tailTrace_1788679 : CollatzResearch.WordTrace tailWord_1788679 prefixEnd_1788679 102050229289279168765169 := by
  unfold tailWord_1788679
  simp only [CollatzResearch.WordTrace]
  refine ⟨65238482686928939897641091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43492321791285959931760727 65238482686928939897641091)
  ·
    refine ⟨97857724030393409846461637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65238482686928939897641091 97857724030393409846461637)
    ·
      refine ⟨18348323255698764346211557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97857724030393409846461637 18348323255698764346211557)
      ·
        refine ⟨3440310610443518314914667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18348323255698764346211557 3440310610443518314914667)
        ·
          refine ⟨5160465915665277472372001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440310610443518314914667 5160465915665277472372001)
          ·
            refine ⟨3870349436748958104279001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160465915665277472372001 3870349436748958104279001)
            ·
              refine ⟨2902762077561718578209251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870349436748958104279001 2902762077561718578209251)
              ·
                refine ⟨4354143116342577867313877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902762077561718578209251 4354143116342577867313877)
                ·
                  refine ⟨102050229289279168765169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4354143116342577867313877 102050229289279168765169)
                  ·
                    rfl

theorem cell23_1788679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 7].length) (baseStart_1788679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788679 prefixEnd_1788679 := by exact prefixLift 1788679
  have htrace : WordTrace (prefixWord ++ tailWord_1788679) baseStart_1788679 baseEnd_1788679 := by
    simpa [prefixWord, tailWord_1788679, baseEnd_1788679] using wordTrace_append hprefix tailTrace_1788679
  have hstable : (prefixWord ++ tailWord_1788679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788679).length < 2 ^ (prefixWord ++ tailWord_1788679).sum := by decide
  have hdescent : baseEnd_1788679 < baseStart_1788679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788690 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1788690 : Nat := 118140960795 + 1788690 * 2 ^ 59
def prefixEnd_1788690 : Nat := 4983230072969 + 3 ^ 40 * 1788690 * 2
def baseEnd_1788690 : Nat := 918457711890711975848971

theorem tailTrace_1788690 : CollatzResearch.WordTrace tailWord_1788690 prefixEnd_1788690 918457711890711975848971 := by
  unfold tailWord_1788690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309720972472272194072881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43492589259926059184194349 16309720972472272194072881)
  ·
    refine ⟨12232290729354204145554661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16309720972472272194072881 12232290729354204145554661)
    ·
      refine ⟨2293554511753913277291499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12232290729354204145554661 2293554511753913277291499)
      ·
        refine ⟨3440331767630869915937249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2293554511753913277291499 3440331767630869915937249)
        ·
          refine ⟨2580248825723152436952937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440331767630869915937249 2580248825723152436952937)
          ·
            refine ⟨1935186619292364327714703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580248825723152436952937 1935186619292364327714703)
            ·
              refine ⟨2902779928938546491572055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935186619292364327714703 2902779928938546491572055)
              ·
                refine ⟨4354169893407819737358083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902779928938546491572055 4354169893407819737358083)
                ·
                  refine ⟨6531254840111729606037125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354169893407819737358083 6531254840111729606037125)
                  ·
                    refine ⟨1224610282520949301131961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531254840111729606037125 1224610282520949301131961)
                    ·
                      refine ⟨918457711890711975848971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224610282520949301131961 918457711890711975848971)
                      ·
                        rfl

theorem cell23_1788690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1788690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788690 prefixEnd_1788690 := by exact prefixLift 1788690
  have htrace : WordTrace (prefixWord ++ tailWord_1788690) baseStart_1788690 baseEnd_1788690 := by
    simpa [prefixWord, tailWord_1788690, baseEnd_1788690] using wordTrace_append hprefix tailTrace_1788690
  have hstable : (prefixWord ++ tailWord_1788690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788690).length < 2 ^ (prefixWord ++ tailWord_1788690).sum := by decide
  have hdescent : baseEnd_1788690 < baseStart_1788690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788790 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1788790 : Nat := 118140960795 + 1788790 * 2 ^ 59
def prefixEnd_1788790 : Nat := 4983230072969 + 3 ^ 40 * 1788790 * 2
def baseEnd_1788790 : Nat := 306169686652053861532837

theorem tailTrace_1788790 : CollatzResearch.WordTrace tailWord_1788790 prefixEnd_1788790 306169686652053861532837 := by
  unfold tailWord_1788790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077658199345425365933239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43495020793017870569954549 4077658199345425365933239)
  ·
    refine ⟨6116487299018138048899859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077658199345425365933239 6116487299018138048899859)
    ·
      refine ⟨9174730948527207073349789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116487299018138048899859 9174730948527207073349789)
      ·
        refine ⟨3440524105697702652506171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9174730948527207073349789 3440524105697702652506171)
        ·
          refine ⟨5160786158546553978759257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440524105697702652506171 5160786158546553978759257)
          ·
            refine ⟨3870589618909915484069443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160786158546553978759257 3870589618909915484069443)
            ·
              refine ⟨5805884428364873226104165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870589618909915484069443 5805884428364873226104165)
              ·
                refine ⟨1088603330318413729894531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5805884428364873226104165 1088603330318413729894531)
                ·
                  refine ⟨1632904995477620594841797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088603330318413729894531 1632904995477620594841797)
                  ·
                    refine ⟨306169686652053861532837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632904995477620594841797 306169686652053861532837)
                    ·
                      rfl

theorem cell23_1788790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1788790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788790 prefixEnd_1788790 := by exact prefixLift 1788790
  have htrace : WordTrace (prefixWord ++ tailWord_1788790) baseStart_1788790 baseEnd_1788790 := by
    simpa [prefixWord, tailWord_1788790, baseEnd_1788790] using wordTrace_append hprefix tailTrace_1788790
  have hstable : (prefixWord ++ tailWord_1788790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788790).length < 2 ^ (prefixWord ++ tailWord_1788790).sum := by decide
  have hdescent : baseEnd_1788790 < baseStart_1788790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788819 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 8, 2]
def baseStart_1788819 : Nat := 118140960795 + 1788819 * 2 ^ 59
def prefixEnd_1788819 : Nat := 4983230072969 + 3 ^ 40 * 1788819 * 2
def baseEnd_1788819 : Nat := 918523950895141971135877

theorem tailTrace_1788819 : CollatzResearch.WordTrace tailWord_1788819 prefixEnd_1788819 918523950895141971135877 := by
  unfold tailWord_1788819
  simp only [CollatzResearch.WordTrace]
  refine ⟨65243588906421743807737511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43495725937614495871825007 65243588906421743807737511)
  ·
    refine ⟨97865383359632615711606267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65243588906421743807737511 97865383359632615711606267)
    ·
      refine ⟨146798075039448923567409401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97865383359632615711606267 146798075039448923567409401)
      ·
        refine ⟨110098556279586692675557051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146798075039448923567409401 110098556279586692675557051)
        ·
          refine ⟨165147834419380039013335577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110098556279586692675557051 165147834419380039013335577)
          ·
            refine ⟨123860875814535029260001683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165147834419380039013335577 123860875814535029260001683)
            ·
              refine ⟨185791313721802543890002525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123860875814535029260001683 185791313721802543890002525)
              ·
                refine ⟨69671742645675953958750947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185791313721802543890002525 69671742645675953958750947)
                ·
                  refine ⟨104507613968513930938126421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69671742645675953958750947 104507613968513930938126421)
                  ·
                    refine ⟨1224698601193522628181169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104507613968513930938126421 1224698601193522628181169)
                    ·
                      refine ⟨918523950895141971135877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224698601193522628181169 918523950895141971135877)
                      ·
                        rfl

theorem cell23_1788819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8, 2].length) (baseStart_1788819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788819 prefixEnd_1788819 := by exact prefixLift 1788819
  have htrace : WordTrace (prefixWord ++ tailWord_1788819) baseStart_1788819 baseEnd_1788819 := by
    simpa [prefixWord, tailWord_1788819, baseEnd_1788819] using wordTrace_append hprefix tailTrace_1788819
  have hstable : (prefixWord ++ tailWord_1788819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788819).length < 2 ^ (prefixWord ++ tailWord_1788819).sum := by decide
  have hdescent : baseEnd_1788819 < baseStart_1788819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788829 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1788829 : Nat := 118140960795 + 1788829 * 2 ^ 59
def prefixEnd_1788829 : Nat := 4983230072969 + 3 ^ 40 * 1788829 * 2
def baseEnd_1788829 : Nat := 306176361900562310670277

theorem tailTrace_1788829 : CollatzResearch.WordTrace tailWord_1788829 prefixEnd_1788829 306176361900562310670277 := by
  unfold tailWord_1788829
  simp only [CollatzResearch.WordTrace]
  refine ⟨65243953636385515515601541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43495969090923677010401027 65243953636385515515601541)
  ·
    refine ⟨12233241306822284159175289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65243953636385515515601541 12233241306822284159175289)
    ·
      refine ⟨9174930980116713119381467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12233241306822284159175289 9174930980116713119381467)
      ·
        refine ⟨13762396470175069679072201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174930980116713119381467 13762396470175069679072201)
        ·
          refine ⟨10321797352631302259304151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13762396470175069679072201 10321797352631302259304151)
          ·
            refine ⟨15482696028946953388956227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10321797352631302259304151 15482696028946953388956227)
            ·
              refine ⟨23224044043420430083434341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15482696028946953388956227 23224044043420430083434341)
              ·
                refine ⟨4354508258141330640643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23224044043420430083434341 4354508258141330640643939)
                ·
                  refine ⟨6531762387211995960965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354508258141330640643939 6531762387211995960965909)
                  ·
                    refine ⟨306176361900562310670277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6531762387211995960965909 306176361900562310670277)
                    ·
                      rfl

theorem cell23_1788829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1788829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788829 prefixEnd_1788829 := by exact prefixLift 1788829
  have htrace : WordTrace (prefixWord ++ tailWord_1788829) baseStart_1788829 baseEnd_1788829 := by
    simpa [prefixWord, tailWord_1788829, baseEnd_1788829] using wordTrace_append hprefix tailTrace_1788829
  have hstable : (prefixWord ++ tailWord_1788829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788829).length < 2 ^ (prefixWord ++ tailWord_1788829).sum := by decide
  have hdescent : baseEnd_1788829 < baseStart_1788829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788833 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_1788833 : Nat := 118140960795 + 1788833 * 2 ^ 59
def prefixEnd_1788833 : Nat := 4983230072969 + 3 ^ 40 * 1788833 * 2
def baseEnd_1788833 : Nat := 306177046541434972120271

theorem tailTrace_1788833 : CollatzResearch.WordTrace tailWord_1788833 prefixEnd_1788833 306177046541434972120271 := by
  unfold tailWord_1788833
  simp only [CollatzResearch.WordTrace]
  refine ⟨65244099528371024198747153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43496066352247349465831435 65244099528371024198747153)
  ·
    refine ⟨48933074646278268149060365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65244099528371024198747153 48933074646278268149060365)
    ·
      refine ⟨18349902992354350555897637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48933074646278268149060365 18349902992354350555897637)
      ·
        refine ⟨3440606811066440729230807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18349902992354350555897637 3440606811066440729230807)
        ·
          refine ⟨5160910216599661093846211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440606811066440729230807 5160910216599661093846211)
          ·
            refine ⟨7741365324899491640769317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160910216599661093846211 7741365324899491640769317)
            ·
              refine ⟨1451505998418654682644247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7741365324899491640769317 1451505998418654682644247)
              ·
                refine ⟨2177258997627982023966371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451505998418654682644247 2177258997627982023966371)
                ·
                  refine ⟨3265888496441973035949557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177258997627982023966371 3265888496441973035949557)
                  ·
                    refine ⟨306177046541434972120271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3265888496441973035949557 306177046541434972120271)
                    ·
                      rfl

theorem cell23_1788833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_1788833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788833 prefixEnd_1788833 := by exact prefixLift 1788833
  have htrace : WordTrace (prefixWord ++ tailWord_1788833) baseStart_1788833 baseEnd_1788833 := by
    simpa [prefixWord, tailWord_1788833, baseEnd_1788833] using wordTrace_append hprefix tailTrace_1788833
  have hstable : (prefixWord ++ tailWord_1788833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788833).length < 2 ^ (prefixWord ++ tailWord_1788833).sum := by decide
  have hdescent : baseEnd_1788833 < baseStart_1788833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788836 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_1788836 : Nat := 118140960795 + 1788836 * 2 ^ 59
def prefixEnd_1788836 : Nat := 4983230072969 + 3 ^ 40 * 1788836 * 2
def baseEnd_1788836 : Nat := 918532680066268404623299

theorem tailTrace_1788836 : CollatzResearch.WordTrace tailWord_1788836 prefixEnd_1788836 918532680066268404623299 := by
  unfold tailWord_1788836
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622104473680077855553181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43496139298240103807404241 32622104473680077855553181)
  ·
    refine ⟨12233289177630029195832443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32622104473680077855553181 12233289177630029195832443)
    ·
      refine ⟨18349933766445043793748665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233289177630029195832443 18349933766445043793748665)
      ·
        refine ⟨13762450324833782845311499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18349933766445043793748665 13762450324833782845311499)
        ·
          refine ⟨20643675487250674267967249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762450324833782845311499 20643675487250674267967249)
          ·
            refine ⟨15482756615438005700975437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20643675487250674267967249 15482756615438005700975437)
            ·
              refine ⟨5806033730789252137865789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15482756615438005700975437 5806033730789252137865789)
              ·
                refine ⟨2177262649045969551699671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806033730789252137865789 2177262649045969551699671)
                ·
                  refine ⟨3265893973568954327549507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177262649045969551699671 3265893973568954327549507)
                  ·
                    refine ⟨4898840960353431491324261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3265893973568954327549507 4898840960353431491324261)
                    ·
                      refine ⟨918532680066268404623299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4898840960353431491324261 918532680066268404623299)
                      ·
                        rfl

theorem cell23_1788836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_1788836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788836 prefixEnd_1788836 := by exact prefixLift 1788836
  have htrace : WordTrace (prefixWord ++ tailWord_1788836) baseStart_1788836 baseEnd_1788836 := by
    simpa [prefixWord, tailWord_1788836, baseEnd_1788836] using wordTrace_append hprefix tailTrace_1788836
  have hstable : (prefixWord ++ tailWord_1788836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788836).length < 2 ^ (prefixWord ++ tailWord_1788836).sum := by decide
  have hdescent : baseEnd_1788836 < baseStart_1788836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788896 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2]
def baseStart_1788896 : Nat := 118140960795 + 1788896 * 2 ^ 59
def prefixEnd_1788896 : Nat := 4983230072969 + 3 ^ 40 * 1788896 * 2
def baseEnd_1788896 : Nat := 918563488905538169873023

theorem tailTrace_1788896 : CollatzResearch.WordTrace tailWord_1788896 prefixEnd_1788896 918563488905538169873023 := by
  unfold tailWord_1788896
  simp only [CollatzResearch.WordTrace]
  refine ⟨32623198663571392979145271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43497598218095190638860361 32623198663571392979145271)
  ·
    refine ⟨48934797995357089468717907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32623198663571392979145271 48934797995357089468717907)
    ·
      refine ⟨73402196993035634203076861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48934797995357089468717907 73402196993035634203076861)
      ·
        refine ⟨27525823872388362826153823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73402196993035634203076861 27525823872388362826153823)
        ·
          refine ⟨41288735808582544239230735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27525823872388362826153823 41288735808582544239230735)
          ·
            refine ⟨61933103712873816358846103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41288735808582544239230735 61933103712873816358846103)
            ·
              refine ⟨92899655569310724538269155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61933103712873816358846103 92899655569310724538269155)
              ·
                refine ⟨139349483353966086807403733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92899655569310724538269155 139349483353966086807403733)
                ·
                  refine ⟨3266003516108580159548525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 139349483353966086807403733 3266003516108580159548525)
                  ·
                    refine ⟨1224751318540717559830697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266003516108580159548525 1224751318540717559830697)
                    ·
                      refine ⟨918563488905538169873023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224751318540717559830697 918563488905538169873023)
                      ·
                        rfl

theorem cell23_1788896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_1788896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788896 prefixEnd_1788896 := by exact prefixLift 1788896
  have htrace : WordTrace (prefixWord ++ tailWord_1788896) baseStart_1788896 baseEnd_1788896 := by
    simpa [prefixWord, tailWord_1788896, baseEnd_1788896] using wordTrace_append hprefix tailTrace_1788896
  have hstable : (prefixWord ++ tailWord_1788896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788896).length < 2 ^ (prefixWord ++ tailWord_1788896).sum := by decide
  have hdescent : baseEnd_1788896 < baseStart_1788896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788899 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1788899 : Nat := 118140960795 + 1788899 * 2 ^ 59
def prefixEnd_1788899 : Nat := 4983230072969 + 3 ^ 40 * 1788899 * 2
def baseEnd_1788899 : Nat := 918565029347501658135509

theorem tailTrace_1788899 : CollatzResearch.WordTrace tailWord_1788899 prefixEnd_1788899 918565029347501658135509 := by
  unfold tailWord_1788899
  simp only [CollatzResearch.WordTrace]
  refine ⟨65246506746131917470649751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43497671164087944980433167 65246506746131917470649751)
  ·
    refine ⟨97869760119197876205974627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65246506746131917470649751 97869760119197876205974627)
    ·
      refine ⟨146804640178796814308961941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97869760119197876205974627 146804640178796814308961941)
      ·
        refine ⟨6881467508381100670732591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146804640178796814308961941 6881467508381100670732591)
        ·
          refine ⟨10322201262571651006098887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881467508381100670732591 10322201262571651006098887)
          ·
            refine ⟨15483301893857476509148331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322201262571651006098887 15483301893857476509148331)
            ·
              refine ⟨23224952840786214763722497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483301893857476509148331 23224952840786214763722497)
              ·
                refine ⟨17418714630589661072791873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23224952840786214763722497 17418714630589661072791873)
                ·
                  refine ⟨13064035972942245804593905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17418714630589661072791873 13064035972942245804593905)
                  ·
                    refine ⟨9798026979706684353445429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13064035972942245804593905 9798026979706684353445429)
                    ·
                      refine ⟨918565029347501658135509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9798026979706684353445429 918565029347501658135509)
                      ·
                        rfl

theorem cell23_1788899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1788899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788899 prefixEnd_1788899 := by exact prefixLift 1788899
  have htrace : WordTrace (prefixWord ++ tailWord_1788899) baseStart_1788899 baseEnd_1788899 := by
    simpa [prefixWord, tailWord_1788899, baseEnd_1788899] using wordTrace_append hprefix tailTrace_1788899
  have hstable : (prefixWord ++ tailWord_1788899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788899).length < 2 ^ (prefixWord ++ tailWord_1788899).sum := by decide
  have hdescent : baseEnd_1788899 < baseStart_1788899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788903 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1788903 : Nat := 118140960795 + 1788903 * 2 ^ 59
def prefixEnd_1788903 : Nat := 4983230072969 + 3 ^ 40 * 1788903 * 2
def baseEnd_1788903 : Nat := 918567083270119642485491

theorem tailTrace_1788903 : CollatzResearch.WordTrace tailWord_1788903 prefixEnd_1788903 918567083270119642485491 := by
  unfold tailWord_1788903
  simp only [CollatzResearch.WordTrace]
  refine ⟨65246652638117426153795363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43497768425411617435863575 65246652638117426153795363)
  ·
    refine ⟨97869978957176139230693045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65246652638117426153795363 97869978957176139230693045)
    ·
      refine ⟨9175310527235263052877473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97869978957176139230693045 9175310527235263052877473)
      ·
        refine ⟨6881482895426447289658105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9175310527235263052877473 6881482895426447289658105)
        ·
          refine ⟨5161112171569835467243579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881482895426447289658105 5161112171569835467243579)
          ·
            refine ⟨7741668257354753200865369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161112171569835467243579 7741668257354753200865369)
            ·
              refine ⟨5806251193016064900649027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741668257354753200865369 5806251193016064900649027)
              ·
                refine ⟨8709376789524097350973541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806251193016064900649027 8709376789524097350973541)
                ·
                  refine ⟨1633008148035768253307539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8709376789524097350973541 1633008148035768253307539)
                  ·
                    refine ⟨2449512222053652379961309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633008148035768253307539 2449512222053652379961309)
                    ·
                      refine ⟨918567083270119642485491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449512222053652379961309 918567083270119642485491)
                      ·
                        rfl

theorem cell23_1788903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1788903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788903 prefixEnd_1788903 := by exact prefixLift 1788903
  have htrace : WordTrace (prefixWord ++ tailWord_1788903) baseStart_1788903 baseEnd_1788903 := by
    simpa [prefixWord, tailWord_1788903, baseEnd_1788903] using wordTrace_append hprefix tailTrace_1788903
  have hstable : (prefixWord ++ tailWord_1788903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788903).length < 2 ^ (prefixWord ++ tailWord_1788903).sum := by decide
  have hdescent : baseEnd_1788903 < baseStart_1788903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788914 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1788914 : Nat := 118140960795 + 1788914 * 2 ^ 59
def prefixEnd_1788914 : Nat := 4983230072969 + 3 ^ 40 * 1788914 * 2
def baseEnd_1788914 : Nat := 306190910519106366482647

theorem tailTrace_1788914 : CollatzResearch.WordTrace tailWord_1788914 prefixEnd_1788914 306190910519106366482647 := by
  unfold tailWord_1788914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16311763460269393758111449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43498035894051716688297197 16311763460269393758111449)
  ·
    refine ⟨12233822595202045318583587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16311763460269393758111449 12233822595202045318583587)
    ·
      refine ⟨18350733892803067977875381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233822595202045318583587 18350733892803067977875381)
      ·
        refine ⟨1720381302450287622925817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18350733892803067977875381 1720381302450287622925817)
        ·
          refine ⟨1290285976837715717194363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720381302450287622925817 1290285976837715717194363)
          ·
            refine ⟨1935428965256573575791545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290285976837715717194363 1935428965256573575791545)
            ·
              refine ⟨1451571723942430181843659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935428965256573575791545 1451571723942430181843659)
              ·
                refine ⟨2177357585913645272765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451571723942430181843659 2177357585913645272765489)
                ·
                  refine ⟨1633018189435233954574117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2177357585913645272765489 1633018189435233954574117)
                  ·
                    refine ⟨306190910519106366482647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633018189435233954574117 306190910519106366482647)
                    ·
                      rfl

theorem cell23_1788914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1788914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788914 prefixEnd_1788914 := by exact prefixLift 1788914
  have htrace : WordTrace (prefixWord ++ tailWord_1788914) baseStart_1788914 baseEnd_1788914 := by
    simpa [prefixWord, tailWord_1788914, baseEnd_1788914] using wordTrace_append hprefix tailTrace_1788914
  have hstable : (prefixWord ++ tailWord_1788914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788914).length < 2 ^ (prefixWord ++ tailWord_1788914).sum := by decide
  have hdescent : baseEnd_1788914 < baseStart_1788914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788976 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_1788976 : Nat := 118140960795 + 1788976 * 2 ^ 59
def prefixEnd_1788976 : Nat := 4983230072969 + 3 ^ 40 * 1788976 * 2
def baseEnd_1788976 : Nat := 918604567357897856872655

theorem tailTrace_1788976 : CollatzResearch.WordTrace tailWord_1788976 prefixEnd_1788976 918604567357897856872655 := by
  unfold tailWord_1788976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624657583426479810601391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43499543444568639747468521 32624657583426479810601391)
  ·
    refine ⟨48936986375139719715902087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32624657583426479810601391 48936986375139719715902087)
    ·
      refine ⟨73405479562709579573853131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48936986375139719715902087 73405479562709579573853131)
      ·
        refine ⟨110108219344064369360779697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73405479562709579573853131 110108219344064369360779697)
        ·
          refine ⟨82581164508048277020584773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110108219344064369360779697 82581164508048277020584773)
          ·
            refine ⟨15483968345259051941359645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82581164508048277020584773 15483968345259051941359645)
            ·
              refine ⟨5806488129472144478009867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15483968345259051941359645 5806488129472144478009867)
              ·
                refine ⟨8709732194208216717014801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806488129472144478009867 8709732194208216717014801)
                ·
                  refine ⟨6532299145656162537761101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709732194208216717014801 6532299145656162537761101)
                  ·
                    refine ⟨2449612179621060951660413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6532299145656162537761101 2449612179621060951660413)
                    ·
                      refine ⟨918604567357897856872655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449612179621060951660413 918604567357897856872655)
                      ·
                        rfl

theorem cell23_1788976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_1788976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788976 prefixEnd_1788976 := by exact prefixLift 1788976
  have htrace : WordTrace (prefixWord ++ tailWord_1788976) baseStart_1788976 baseEnd_1788976 := by
    simpa [prefixWord, tailWord_1788976, baseEnd_1788976] using wordTrace_append hprefix tailTrace_1788976
  have hstable : (prefixWord ++ tailWord_1788976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788976).length < 2 ^ (prefixWord ++ tailWord_1788976).sum := by decide
  have hdescent : baseEnd_1788976 < baseStart_1788976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788979 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 7]
def baseStart_1788979 : Nat := 118140960795 + 1788979 * 2 ^ 59
def prefixEnd_1788979 : Nat := 4983230072969 + 3 ^ 40 * 1788979 * 2
def baseEnd_1788979 : Nat := 306202035933287115045047

theorem tailTrace_1788979 : CollatzResearch.WordTrace tailWord_1788979 prefixEnd_1788979 306202035933287115045047 := by
  unfold tailWord_1788979
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249424585842091133561991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43499616390561394089041327 65249424585842091133561991)
  ·
    refine ⟨97874136878763136700342987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65249424585842091133561991 97874136878763136700342987)
    ·
      refine ⟨146811205318144705050514481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97874136878763136700342987 146811205318144705050514481)
      ·
        refine ⟨110108403988608528787885861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146811205318144705050514481 110108403988608528787885861)
        ·
          refine ⟨20645325747864099147728599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110108403988608528787885861 20645325747864099147728599)
          ·
            refine ⟨30967988621796148721592899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20645325747864099147728599 30967988621796148721592899)
            ·
              refine ⟨46451982932694223082389349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30967988621796148721592899 46451982932694223082389349)
              ·
                refine ⟨8709746799880166827948003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46451982932694223082389349 8709746799880166827948003)
                ·
                  refine ⟨13064620199820250241922005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8709746799880166827948003 13064620199820250241922005)
                  ·
                    refine ⟨306202035933287115045047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13064620199820250241922005 306202035933287115045047)
                    ·
                      rfl

theorem cell23_1788979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_1788979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1788979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1788979 prefixEnd_1788979 := by exact prefixLift 1788979
  have htrace : WordTrace (prefixWord ++ tailWord_1788979) baseStart_1788979 baseEnd_1788979 := by
    simpa [prefixWord, tailWord_1788979, baseEnd_1788979] using wordTrace_append hprefix tailTrace_1788979
  have hstable : (prefixWord ++ tailWord_1788979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788979).length < 2 ^ (prefixWord ++ tailWord_1788979).sum := by decide
  have hdescent : baseEnd_1788979 < baseStart_1788979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789016 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1789016 : Nat := 118140960795 + 1789016 * 2 ^ 59
def prefixEnd_1789016 : Nat := 4983230072969 + 3 ^ 40 * 1789016 * 2
def baseEnd_1789016 : Nat := 918625106584077700372471

theorem tailTrace_1789016 : CollatzResearch.WordTrace tailWord_1789016 prefixEnd_1789016 918625106584077700372471 := by
  unfold tailWord_1789016
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625387043354023226329451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43500516057805364301772601 32625387043354023226329451)
  ·
    refine ⟨48938080565031034839494177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32625387043354023226329451 48938080565031034839494177)
    ·
      refine ⟨36703560423773276129620633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48938080565031034839494177 36703560423773276129620633)
      ·
        refine ⟨27527670317829957097215475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36703560423773276129620633 27527670317829957097215475)
        ·
          refine ⟨41291505476744935645823213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527670317829957097215475 41291505476744935645823213)
          ·
            refine ⟨15484314553779350867183705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41291505476744935645823213 15484314553779350867183705)
            ·
              refine ⟨11613235915334513150387779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484314553779350867183705 11613235915334513150387779)
              ·
                refine ⟨17419853873001769725581669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613235915334513150387779 17419853873001769725581669)
                ·
                  refine ⟨3266222601187831823546563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17419853873001769725581669 3266222601187831823546563)
                  ·
                    refine ⟨4899333901781747735319845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3266222601187831823546563 4899333901781747735319845)
                    ·
                      refine ⟨918625106584077700372471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4899333901781747735319845 918625106584077700372471)
                      ·
                        rfl

theorem cell23_1789016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1789016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789016 prefixEnd_1789016 := by exact prefixLift 1789016
  have htrace : WordTrace (prefixWord ++ tailWord_1789016) baseStart_1789016 baseEnd_1789016 := by
    simpa [prefixWord, tailWord_1789016, baseEnd_1789016] using wordTrace_append hprefix tailTrace_1789016
  have hstable : (prefixWord ++ tailWord_1789016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789016).length < 2 ^ (prefixWord ++ tailWord_1789016).sum := by decide
  have hdescent : baseEnd_1789016 < baseStart_1789016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789033 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 4, 2]
def baseStart_1789033 : Nat := 118140960795 + 1789033 * 2 ^ 59
def prefixEnd_1789033 : Nat := 4983230072969 + 3 ^ 40 * 1789033 * 2
def baseEnd_1789033 : Nat := 918633835755204133859893

theorem tailTrace_1789033 : CollatzResearch.WordTrace tailWord_1789033 prefixEnd_1789033 918633835755204133859893 := by
  unfold tailWord_1789033
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251394127646458356027753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43500929418430972237351835 65251394127646458356027753)
  ·
    refine ⟨48938545595734843767020815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65251394127646458356027753 48938545595734843767020815)
    ·
      refine ⟨73407818393602265650531223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48938545595734843767020815 73407818393602265650531223)
      ·
        refine ⟨110111727590403398475796835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73407818393602265650531223 110111727590403398475796835)
        ·
          refine ⟨165167591385605097713695253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110111727590403398475796835 165167591385605097713695253)
          ·
            refine ⟨7742230846200238955329465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165167591385605097713695253 7742230846200238955329465)
            ·
              refine ⟨5806673134650179216497099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7742230846200238955329465 5806673134650179216497099)
              ·
                refine ⟨8710009701975268824745649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806673134650179216497099 8710009701975268824745649)
                ·
                  refine ⟨6532507276481451618559237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8710009701975268824745649 6532507276481451618559237)
                  ·
                    refine ⟨1224845114340272178479857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532507276481451618559237 1224845114340272178479857)
                    ·
                      refine ⟨918633835755204133859893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224845114340272178479857 918633835755204133859893)
                      ·
                        rfl

theorem cell23_1789033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4, 2].length) (baseStart_1789033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789033 prefixEnd_1789033 := by exact prefixLift 1789033
  have htrace : WordTrace (prefixWord ++ tailWord_1789033) baseStart_1789033 baseEnd_1789033 := by
    simpa [prefixWord, tailWord_1789033, baseEnd_1789033] using wordTrace_append hprefix tailTrace_1789033
  have hstable : (prefixWord ++ tailWord_1789033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789033).length < 2 ^ (prefixWord ++ tailWord_1789033).sum := by decide
  have hdescent : baseEnd_1789033 < baseStart_1789033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789036 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1789036 : Nat := 118140960795 + 1789036 * 2 ^ 59
def prefixEnd_1789036 : Nat := 4983230072969 + 3 ^ 40 * 1789036 * 2
def baseEnd_1789036 : Nat := 918635376197167622122379

theorem tailTrace_1789036 : CollatzResearch.WordTrace tailWord_1789036 prefixEnd_1789036 918635376197167622122379 := by
  unfold tailWord_1789036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625751773317794934193481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43501002364423726578924641 32625751773317794934193481)
  ·
    refine ⟨24469313829988346200645111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32625751773317794934193481 24469313829988346200645111)
    ·
      refine ⟨36703970744982519300967667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24469313829988346200645111 36703970744982519300967667)
      ·
        refine ⟨55055956117473778951451501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36703970744982519300967667 55055956117473778951451501)
        ·
          refine ⟨20645983544052667106794313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55055956117473778951451501 20645983544052667106794313)
          ·
            refine ⟨15484487658039500330095735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20645983544052667106794313 15484487658039500330095735)
            ·
              refine ⟨23226731487059250495143603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15484487658039500330095735 23226731487059250495143603)
              ·
                refine ⟨34840097230588875742715405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23226731487059250495143603 34840097230588875742715405)
                ·
                  refine ⟨13065036461470828403518277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34840097230588875742715405 13065036461470828403518277)
                  ·
                    refine ⟨2449694336525780325659677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13065036461470828403518277 2449694336525780325659677)
                    ·
                      refine ⟨918635376197167622122379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449694336525780325659677 918635376197167622122379)
                      ·
                        rfl

theorem cell23_1789036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1789036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789036 prefixEnd_1789036 := by exact prefixLift 1789036
  have htrace : WordTrace (prefixWord ++ tailWord_1789036) baseStart_1789036 baseEnd_1789036 := by
    simpa [prefixWord, tailWord_1789036, baseEnd_1789036] using wordTrace_append hprefix tailTrace_1789036
  have hstable : (prefixWord ++ tailWord_1789036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789036).length < 2 ^ (prefixWord ++ tailWord_1789036).sum := by decide
  have hdescent : baseEnd_1789036 < baseStart_1789036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789053 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1789053 : Nat := 118140960795 + 1789053 * 2 ^ 59
def prefixEnd_1789053 : Nat := 4983230072969 + 3 ^ 40 * 1789053 * 2
def baseEnd_1789053 : Nat := 918644105368294055609801

theorem tailTrace_1789053 : CollatzResearch.WordTrace tailWord_1789053 prefixEnd_1789053 918644105368294055609801 := by
  unfold tailWord_1789053
  simp only [CollatzResearch.WordTrace]
  refine ⟨65252123587574001771755813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43501415725049334514503875 65252123587574001771755813)
  ·
    refine ⟨12234773172670125332204215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65252123587574001771755813 12234773172670125332204215)
    ·
      refine ⟨18352159759005187998306323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234773172670125332204215 18352159759005187998306323)
      ·
        refine ⟨27528239638507781997459485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352159759005187998306323 27528239638507781997459485)
        ·
          refine ⟨10323089864440418249047307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27528239638507781997459485 10323089864440418249047307)
          ·
            refine ⟨15484634796660627373570961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323089864440418249047307 15484634796660627373570961)
            ·
              refine ⟨11613476097495470530178221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484634796660627373570961 11613476097495470530178221)
              ·
                refine ⟨4355053536560801448816833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11613476097495470530178221 4355053536560801448816833)
                ·
                  refine ⟨3266290152420601086612625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355053536560801448816833 3266290152420601086612625)
                  ·
                    refine ⟨2449717614315450814959469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266290152420601086612625 2449717614315450814959469)
                    ·
                      refine ⟨918644105368294055609801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449717614315450814959469 918644105368294055609801)
                      ·
                        rfl

theorem cell23_1789053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1789053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789053 prefixEnd_1789053 := by exact prefixLift 1789053
  have htrace : WordTrace (prefixWord ++ tailWord_1789053) baseStart_1789053 baseEnd_1789053 := by
    simpa [prefixWord, tailWord_1789053, baseEnd_1789053] using wordTrace_append hprefix tailTrace_1789053
  have hstable : (prefixWord ++ tailWord_1789053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789053).length < 2 ^ (prefixWord ++ tailWord_1789053).sum := by decide
  have hdescent : baseEnd_1789053 < baseStart_1789053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789070 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1789070 : Nat := 118140960795 + 1789070 * 2 ^ 59
def prefixEnd_1789070 : Nat := 4983230072969 + 3 ^ 40 * 1789070 * 2
def baseEnd_1789070 : Nat := 918652834539420489097223

theorem tailTrace_1789070 : CollatzResearch.WordTrace tailWord_1789070 prefixEnd_1789070 918652834539420489097223 := by
  unfold tailWord_1789070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156592953564051709390583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43501829085674942450083109 8156592953564051709390583)
  ·
    refine ⟨12234889430346077564085875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156592953564051709390583 12234889430346077564085875)
    ·
      refine ⟨18352334145519116346128813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234889430346077564085875 18352334145519116346128813)
      ·
        refine ⟨6882125304569668629798305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18352334145519116346128813 6882125304569668629798305)
        ·
          refine ⟨5161593978427251472348729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882125304569668629798305 5161593978427251472348729)
          ·
            refine ⟨3871195483820438604261547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5161593978427251472348729 3871195483820438604261547)
            ·
              refine ⟨5806793225730657906392321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871195483820438604261547 5806793225730657906392321)
              ·
                refine ⟨4355094919297993429794241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806793225730657906392321 4355094919297993429794241)
                ·
                  refine ⟨3266321189473495072345681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355094919297993429794241 3266321189473495072345681)
                  ·
                    refine ⟨2449740892105121304259261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266321189473495072345681 2449740892105121304259261)
                    ·
                      refine ⟨918652834539420489097223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449740892105121304259261 918652834539420489097223)
                      ·
                        rfl

theorem cell23_1789070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1789070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789070 prefixEnd_1789070 := by exact prefixLift 1789070
  have htrace : WordTrace (prefixWord ++ tailWord_1789070) baseStart_1789070 baseEnd_1789070 := by
    simpa [prefixWord, tailWord_1789070, baseEnd_1789070] using wordTrace_append hprefix tailTrace_1789070
  have hstable : (prefixWord ++ tailWord_1789070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789070).length < 2 ^ (prefixWord ++ tailWord_1789070).sum := by decide
  have hdescent : baseEnd_1789070 < baseStart_1789070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789090 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1789090 : Nat := 118140960795 + 1789090 * 2 ^ 59
def prefixEnd_1789090 : Nat := 4983230072969 + 3 ^ 40 * 1789090 * 2
def baseEnd_1789090 : Nat := 102073678239167823427459

theorem tailTrace_1789090 : CollatzResearch.WordTrace tailWord_1789090 prefixEnd_1789090 102073678239167823427459 := by
  unfold tailWord_1789090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313368272109989272713181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43502315392293304727235149 16313368272109989272713181)
  ·
    refine ⟨6117513102041245977267443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16313368272109989272713181 6117513102041245977267443)
    ·
      refine ⟨9176269653061868965901165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117513102041245977267443 9176269653061868965901165)
      ·
        refine ⟨3441101119898200862212937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9176269653061868965901165 3441101119898200862212937)
        ·
          refine ⟨2580825839923650646659703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441101119898200862212937 2580825839923650646659703)
          ·
            refine ⟨3871238759885475969989555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580825839923650646659703 3871238759885475969989555)
            ·
              refine ⟨5806858139828213954984333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871238759885475969989555 5806858139828213954984333)
              ·
                refine ⟨2177571802435580233119125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806858139828213954984333 2177571802435580233119125)
                ·
                  refine ⟨102073678239167823427459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2177571802435580233119125 102073678239167823427459)
                  ·
                    rfl

theorem cell23_1789090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1789090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789090 prefixEnd_1789090 := by exact prefixLift 1789090
  have htrace : WordTrace (prefixWord ++ tailWord_1789090) baseStart_1789090 baseEnd_1789090 := by
    simpa [prefixWord, tailWord_1789090, baseEnd_1789090] using wordTrace_append hprefix tailTrace_1789090
  have hstable : (prefixWord ++ tailWord_1789090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789090).length < 2 ^ (prefixWord ++ tailWord_1789090).sum := by decide
  have hdescent : baseEnd_1789090 < baseStart_1789090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789103 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 1, 5]
def baseStart_1789103 : Nat := 118140960795 + 1789103 * 2 ^ 59
def prefixEnd_1789103 : Nat := 4983230072969 + 3 ^ 40 * 1789103 * 2
def baseEnd_1789103 : Nat := 306223259800339619994857

theorem tailTrace_1789103 : CollatzResearch.WordTrace tailWord_1789103 prefixEnd_1789103 306223259800339619994857 := by
  unfold tailWord_1789103
  simp only [CollatzResearch.WordTrace]
  refine ⟨65253947237392860311075963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43502631491595240207383975 65253947237392860311075963)
  ·
    refine ⟨97880920856089290466613945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65253947237392860311075963 97880920856089290466613945)
    ·
      refine ⟨73410690642066967849960459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97880920856089290466613945 73410690642066967849960459)
      ·
        refine ⟨110116035963100451774940689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73410690642066967849960459 110116035963100451774940689)
        ·
          refine ⟨82587026972325338831205517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110116035963100451774940689 82587026972325338831205517)
          ·
            refine ⟨30970135114622002061702069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82587026972325338831205517 30970135114622002061702069)
            ·
              refine ⟨2903450166995812693284569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30970135114622002061702069 2903450166995812693284569)
              ·
                refine ⟨2177587625246859519963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903450166995812693284569 2177587625246859519963427)
                ·
                  refine ⟨3266381437870289279945141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177587625246859519963427 3266381437870289279945141)
                  ·
                    refine ⟨306223259800339619994857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3266381437870289279945141 306223259800339619994857)
                    ·
                      rfl

theorem cell23_1789103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_1789103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789103 prefixEnd_1789103 := by exact prefixLift 1789103
  have htrace : WordTrace (prefixWord ++ tailWord_1789103) baseStart_1789103 baseEnd_1789103 := by
    simpa [prefixWord, tailWord_1789103, baseEnd_1789103] using wordTrace_append hprefix tailTrace_1789103
  have hstable : (prefixWord ++ tailWord_1789103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789103).length < 2 ^ (prefixWord ++ tailWord_1789103).sum := by decide
  have hdescent : baseEnd_1789103 < baseStart_1789103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789134 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_1789134 : Nat := 118140960795 + 1789134 * 2 ^ 59
def prefixEnd_1789134 : Nat := 4983230072969 + 3 ^ 40 * 1789134 * 2
def baseEnd_1789134 : Nat := 918685697301308238696929

theorem tailTrace_1789134 : CollatzResearch.WordTrace tailWord_1789134 prefixEnd_1789134 918685697301308238696929 := by
  unfold tailWord_1789134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156884737535069075681807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43503385266853701736969637 8156884737535069075681807)
  ·
    refine ⟨12235327106302603613522711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156884737535069075681807 12235327106302603613522711)
    ·
      refine ⟨18352990659453905420284067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235327106302603613522711 18352990659453905420284067)
      ·
        refine ⟨27529485989180858130426101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352990659453905420284067 27529485989180858130426101)
        ·
          refine ⟨2580889311485705449727447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27529485989180858130426101 2580889311485705449727447)
          ·
            refine ⟨3871333967228558174591171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580889311485705449727447 3871333967228558174591171)
            ·
              refine ⟨5807000950842837261886757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871333967228558174591171 5807000950842837261886757)
              ·
                refine ⟨1088812678283031986603767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5807000950842837261886757 1088812678283031986603767)
                ·
                  refine ⟨1633219017424547979905651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088812678283031986603767 1633219017424547979905651)
                  ·
                    refine ⟨2449828526136821969858477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633219017424547979905651 2449828526136821969858477)
                    ·
                      refine ⟨918685697301308238696929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449828526136821969858477 918685697301308238696929)
                      ·
                        rfl

theorem cell23_1789134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_1789134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789134 prefixEnd_1789134 := by exact prefixLift 1789134
  have htrace : WordTrace (prefixWord ++ tailWord_1789134) baseStart_1789134 baseEnd_1789134 := by
    simpa [prefixWord, tailWord_1789134, baseEnd_1789134] using wordTrace_append hprefix tailTrace_1789134
  have hstable : (prefixWord ++ tailWord_1789134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789134).length < 2 ^ (prefixWord ++ tailWord_1789134).sum := by decide
  have hdescent : baseEnd_1789134 < baseStart_1789134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789143 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1789143 : Nat := 118140960795 + 1789143 * 2 ^ 59
def prefixEnd_1789143 : Nat := 4983230072969 + 3 ^ 40 * 1789143 * 2
def baseEnd_1789143 : Nat := 918690318627198703484387

theorem tailTrace_1789143 : CollatzResearch.WordTrace tailWord_1789143 prefixEnd_1789143 918690318627198703484387 := by
  unfold tailWord_1789143
  simp only [CollatzResearch.WordTrace]
  refine ⟨65255406157247947142532083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43503604104831964761688055 65255406157247947142532083)
  ·
    refine ⟨97883109235871920713798125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65255406157247947142532083 97883109235871920713798125)
    ·
      refine ⟨36706165963451970267674297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97883109235871920713798125 36706165963451970267674297)
      ·
        refine ⟨27529624472588977700755723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36706165963451970267674297 27529624472588977700755723)
        ·
          refine ⟨41294436708883466551133585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27529624472588977700755723 41294436708883466551133585)
          ·
            refine ⟨30970827531662599913350189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41294436708883466551133585 30970827531662599913350189)
            ·
              refine ⟨11614060324373474967506321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30970827531662599913350189 11614060324373474967506321)
              ·
                refine ⟨8710545243280106225629741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614060324373474967506321 8710545243280106225629741)
                ·
                  refine ⟨3266454466230039834611153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710545243280106225629741 3266454466230039834611153)
                  ·
                    refine ⟨2449840849672529875958365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266454466230039834611153 2449840849672529875958365)
                    ·
                      refine ⟨918690318627198703484387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449840849672529875958365 918690318627198703484387)
                      ·
                        rfl

theorem cell23_1789143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1789143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789143 prefixEnd_1789143 := by exact prefixLift 1789143
  have htrace : WordTrace (prefixWord ++ tailWord_1789143) baseStart_1789143 baseEnd_1789143 := by
    simpa [prefixWord, tailWord_1789143, baseEnd_1789143] using wordTrace_append hprefix tailTrace_1789143
  have hstable : (prefixWord ++ tailWord_1789143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789143).length < 2 ^ (prefixWord ++ tailWord_1789143).sum := by decide
  have hdescent : baseEnd_1789143 < baseStart_1789143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789153 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1789153 : Nat := 118140960795 + 1789153 * 2 ^ 59
def prefixEnd_1789153 : Nat := 4983230072969 + 3 ^ 40 * 1789153 * 2
def baseEnd_1789153 : Nat := 918695453433743664359341

theorem tailTrace_1789153 : CollatzResearch.WordTrace tailWord_1789153 prefixEnd_1789153 918695453433743664359341 := by
  unfold tailWord_1789153
  simp only [CollatzResearch.WordTrace]
  refine ⟨65255770887211718850396113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43503847258141145900264075 65255770887211718850396113)
  ·
    refine ⟨48941828165408789137797085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65255770887211718850396113 48941828165408789137797085)
    ·
      refine ⟨18353185562028295926673907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48941828165408789137797085 18353185562028295926673907)
      ·
        refine ⟨27529778343042443890010861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353185562028295926673907 27529778343042443890010861)
        ·
          refine ⟨10323666878640916458754073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27529778343042443890010861 10323666878640916458754073)
          ·
            refine ⟨7742750158980687344065555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10323666878640916458754073 7742750158980687344065555)
            ·
              refine ⟨11614125238471031016098333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742750158980687344065555 11614125238471031016098333)
              ·
                refine ⟨4355296964426636631036875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11614125238471031016098333 4355296964426636631036875)
                ·
                  refine ⟨6532945446639954946555313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355296964426636631036875 6532945446639954946555313)
                  ·
                    refine ⟨4899709084979966209916485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6532945446639954946555313 4899709084979966209916485)
                    ·
                      refine ⟨918695453433743664359341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4899709084979966209916485 918695453433743664359341)
                      ·
                        rfl

theorem cell23_1789153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1789153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789153 prefixEnd_1789153 := by exact prefixLift 1789153
  have htrace : WordTrace (prefixWord ++ tailWord_1789153) baseStart_1789153 baseEnd_1789153 := by
    simpa [prefixWord, tailWord_1789153, baseEnd_1789153] using wordTrace_append hprefix tailTrace_1789153
  have hstable : (prefixWord ++ tailWord_1789153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789153).length < 2 ^ (prefixWord ++ tailWord_1789153).sum := by decide
  have hdescent : baseEnd_1789153 < baseStart_1789153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789160 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1789160 : Nat := 118140960795 + 1789160 * 2 ^ 59
def prefixEnd_1789160 : Nat := 4983230072969 + 3 ^ 40 * 1789160 * 2
def baseEnd_1789160 : Nat := 918699047798325136971809

theorem tailTrace_1789160 : CollatzResearch.WordTrace tailWord_1789160 prefixEnd_1789160 918699047798325136971809 := by
  unfold tailWord_1789160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32628013099093179522950467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43504017465457572697267289 32628013099093179522950467)
  ·
    refine ⟨48942019648639769284425701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32628013099093179522950467 48942019648639769284425701)
    ·
      refine ⟨9176628684119956740829819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48942019648639769284425701 9176628684119956740829819)
      ·
        refine ⟨13764943026179935111244729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9176628684119956740829819 13764943026179935111244729)
        ·
          refine ⟨10323707269634951333433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13764943026179935111244729 10323707269634951333433547)
          ·
            refine ⟨15485560904452427000150321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323707269634951333433547 15485560904452427000150321)
            ·
              refine ⟨11614170678339320250112741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15485560904452427000150321 11614170678339320250112741)
              ·
                refine ⟨2177657002188622546896139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11614170678339320250112741 2177657002188622546896139)
                ·
                  refine ⟨3266485503282933820344209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177657002188622546896139 3266485503282933820344209)
                  ·
                    refine ⟨2449864127462200365258157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266485503282933820344209 2449864127462200365258157)
                    ·
                      refine ⟨918699047798325136971809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2449864127462200365258157 918699047798325136971809)
                      ·
                        rfl

theorem cell23_1789160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1789160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789160 prefixEnd_1789160 := by exact prefixLift 1789160
  have htrace : WordTrace (prefixWord ++ tailWord_1789160) baseStart_1789160 baseEnd_1789160 := by
    simpa [prefixWord, tailWord_1789160, baseEnd_1789160] using wordTrace_append hprefix tailTrace_1789160
  have hstable : (prefixWord ++ tailWord_1789160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789160).length < 2 ^ (prefixWord ++ tailWord_1789160).sum := by decide
  have hdescent : baseEnd_1789160 < baseStart_1789160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789163 : List Nat := [1, 1, 1, 1, 2, 7, 3, 7]
def baseStart_1789163 : Nat := 118140960795 + 1789163 * 2 ^ 59
def prefixEnd_1789163 : Nat := 4983230072969 + 3 ^ 40 * 1789163 * 2
def baseEnd_1789163 : Nat := 34025947712603282416085

theorem tailTrace_1789163 : CollatzResearch.WordTrace tailWord_1789163 prefixEnd_1789163 34025947712603282416085 := by
  unfold tailWord_1789163
  simp only [CollatzResearch.WordTrace]
  refine ⟨65256135617175490558260143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43504090411450327038840095 65256135617175490558260143)
  ·
    refine ⟨97884203425763235837390215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65256135617175490558260143 97884203425763235837390215)
    ·
      refine ⟨146826305138644853756085323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97884203425763235837390215 146826305138644853756085323)
      ·
        refine ⟨220239457707967280634127985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146826305138644853756085323 220239457707967280634127985)
        ·
          refine ⟨165179593280975460475595989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220239457707967280634127985 165179593280975460475595989)
          ·
            refine ⟨3871396717522862354896781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165179593280975460475595989 3871396717522862354896781)
            ·
              refine ⟨1451773769071073383086293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871396717522862354896781 1451773769071073383086293)
              ·
                refine ⟨34025947712603282416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1451773769071073383086293 34025947712603282416085)
                ·
                  rfl

theorem cell23_1789163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 7].length) (baseStart_1789163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789163 prefixEnd_1789163 := by exact prefixLift 1789163
  have htrace : WordTrace (prefixWord ++ tailWord_1789163) baseStart_1789163 baseEnd_1789163 := by
    simpa [prefixWord, tailWord_1789163, baseEnd_1789163] using wordTrace_append hprefix tailTrace_1789163
  have hstable : (prefixWord ++ tailWord_1789163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789163).length < 2 ^ (prefixWord ++ tailWord_1789163).sum := by decide
  have hdescent : baseEnd_1789163 < baseStart_1789163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789214 : List Nat := [4, 3, 2, 1, 2, 2, 2, 7]
def baseStart_1789214 : Nat := 118140960795 + 1789214 * 2 ^ 59
def prefixEnd_1789214 : Nat := 4983230072969 + 3 ^ 40 * 1789214 * 2
def baseEnd_1789214 : Nat := 34026917620506219470243

theorem tailTrace_1789214 : CollatzResearch.WordTrace tailWord_1789214 prefixEnd_1789214 34026917620506219470243 := by
  unfold tailWord_1789214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157249467498840783545837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43505330493327150845577797 8157249467498840783545837)
  ·
    refine ⟨3058968550312065293829689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8157249467498840783545837 3058968550312065293829689)
    ·
      refine ⟨2294226412734048970372267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3058968550312065293829689 2294226412734048970372267)
      ·
        refine ⟨3441339619101073455558401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294226412734048970372267 3441339619101073455558401)
        ·
          refine ⟨2581004714325805091668801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441339619101073455558401 2581004714325805091668801)
          ·
            refine ⟨1935753535744353818751601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581004714325805091668801 1935753535744353818751601)
            ·
              refine ⟨1451815151808265364063701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935753535744353818751601 1451815151808265364063701)
              ·
                refine ⟨34026917620506219470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1451815151808265364063701 34026917620506219470243)
                ·
                  rfl

theorem cell23_1789214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_1789214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789214 prefixEnd_1789214 := by exact prefixLift 1789214
  have htrace : WordTrace (prefixWord ++ tailWord_1789214) baseStart_1789214 baseEnd_1789214 := by
    simpa [prefixWord, tailWord_1789214, baseEnd_1789214] using wordTrace_append hprefix tailTrace_1789214
  have hstable : (prefixWord ++ tailWord_1789214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789214).length < 2 ^ (prefixWord ++ tailWord_1789214).sum := by decide
  have hdescent : baseEnd_1789214 < baseStart_1789214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789233 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1789233 : Nat := 118140960795 + 1789233 * 2 ^ 59
def prefixEnd_1789233 : Nat := 4983230072969 + 3 ^ 40 * 1789233 * 2
def baseEnd_1789233 : Nat := 918736531886103351358973

theorem tailTrace_1789233 : CollatzResearch.WordTrace tailWord_1789233 prefixEnd_1789233 918736531886103351358973 := by
  unfold tailWord_1789233
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258688726921892513308353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43505792484614595008872235 65258688726921892513308353)
  ·
    refine ⟨48944016545191419384981265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65258688726921892513308353 48944016545191419384981265)
    ·
      refine ⟨36708012408893564538735949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48944016545191419384981265 36708012408893564538735949)
      ·
        refine ⟨13765504653335086702025981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36708012408893564538735949 13765504653335086702025981)
        ·
          refine ⟨5162064245000657513259743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13765504653335086702025981 5162064245000657513259743)
          ·
            refine ⟨7743096367500986269889615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162064245000657513259743 7743096367500986269889615)
            ·
              refine ⟨11614644551251479404834423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743096367500986269889615 11614644551251479404834423)
              ·
                refine ⟨17421966826877219107251635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614644551251479404834423 17421966826877219107251635)
                ·
                  refine ⟨26132950240315828660877453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17421966826877219107251635 26132950240315828660877453)
                  ·
                    refine ⟨9799856340118435747829045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26132950240315828660877453 9799856340118435747829045)
                    ·
                      refine ⟨918736531886103351358973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9799856340118435747829045 918736531886103351358973)
                      ·
                        rfl

theorem cell23_1789233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1789233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789233 prefixEnd_1789233 := by exact prefixLift 1789233
  have htrace : WordTrace (prefixWord ++ tailWord_1789233) baseStart_1789233 baseEnd_1789233 := by
    simpa [prefixWord, tailWord_1789233, baseEnd_1789233] using wordTrace_append hprefix tailTrace_1789233
  have hstable : (prefixWord ++ tailWord_1789233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789233).length < 2 ^ (prefixWord ++ tailWord_1789233).sum := by decide
  have hdescent : baseEnd_1789233 < baseStart_1789233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789247 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 4, 2, 2]
def baseStart_1789247 : Nat := 118140960795 + 1789247 * 2 ^ 59
def prefixEnd_1789247 : Nat := 4983230072969 + 3 ^ 40 * 1789247 * 2
def baseEnd_1789247 : Nat := 918743720615266296583909

theorem tailTrace_1789247 : CollatzResearch.WordTrace tailWord_1789247 prefixEnd_1789247 918743720615266296583909 := by
  unfold tailWord_1789247
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259199348871172904317995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43506132899247448602878663 65259199348871172904317995)
  ·
    refine ⟨97888799023306759356476993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65259199348871172904317995 97888799023306759356476993)
    ·
      refine ⟨73416599267480069517357745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97888799023306759356476993 73416599267480069517357745)
      ·
        refine ⟨55062449450610052138018309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73416599267480069517357745 55062449450610052138018309)
        ·
          refine ⟨10324209271989384775878433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55062449450610052138018309 10324209271989384775878433)
          ·
            refine ⟨7743156953992038581908825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10324209271989384775878433 7743156953992038581908825)
            ·
              refine ⟨5807367715494028936431619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743156953992038581908825 5807367715494028936431619)
              ·
                refine ⟨8711051573241043404647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807367715494028936431619 8711051573241043404647429)
                ·
                  refine ⟨1633322169982695638371393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8711051573241043404647429 1633322169982695638371393)
                  ·
                    refine ⟨1224991627487021728778545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1633322169982695638371393 1224991627487021728778545)
                    ·
                      refine ⟨918743720615266296583909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1224991627487021728778545 918743720615266296583909)
                      ·
                        rfl

theorem cell23_1789247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_1789247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789247 prefixEnd_1789247 := by exact prefixLift 1789247
  have htrace : WordTrace (prefixWord ++ tailWord_1789247) baseStart_1789247 baseEnd_1789247 := by
    simpa [prefixWord, tailWord_1789247, baseEnd_1789247] using wordTrace_append hprefix tailTrace_1789247
  have hstable : (prefixWord ++ tailWord_1789247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789247).length < 2 ^ (prefixWord ++ tailWord_1789247).sum := by decide
  have hdescent : baseEnd_1789247 < baseStart_1789247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789263 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_1789263 : Nat := 118140960795 + 1789263 * 2 ^ 59
def prefixEnd_1789263 : Nat := 4983230072969 + 3 ^ 40 * 1789263 * 2
def baseEnd_1789263 : Nat := 918751936305738233983835

theorem tailTrace_1789263 : CollatzResearch.WordTrace tailWord_1789263 prefixEnd_1789263 918751936305738233983835 := by
  unfold tailWord_1789263
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259782916813207636900443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43506521944542138424600295 65259782916813207636900443)
  ·
    refine ⟨97889674375219811455350665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65259782916813207636900443 97889674375219811455350665)
    ·
      refine ⟨73417255781414858591512999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97889674375219811455350665 73417255781414858591512999)
      ·
        refine ⟨110125883672122287887269499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73417255781414858591512999 110125883672122287887269499)
        ·
          refine ⟨165188825508183431830904249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110125883672122287887269499 165188825508183431830904249)
          ·
            refine ⟨123891619131137573873178187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165188825508183431830904249 123891619131137573873178187)
            ·
              refine ⟨185837428696706360809767281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123891619131137573873178187 185837428696706360809767281)
              ·
                refine ⟨139378071522529770607325461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185837428696706360809767281 139378071522529770607325461)
                ·
                  refine ⟨6533347102618582997218381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139378071522529770607325461 6533347102618582997218381)
                  ·
                    refine ⟨2450005163481968623956893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533347102618582997218381 2450005163481968623956893)
                    ·
                      refine ⟨918751936305738233983835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450005163481968623956893 918751936305738233983835)
                      ·
                        rfl

theorem cell23_1789263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_1789263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789263 prefixEnd_1789263 := by exact prefixLift 1789263
  have htrace : WordTrace (prefixWord ++ tailWord_1789263) baseStart_1789263 baseEnd_1789263 := by
    simpa [prefixWord, tailWord_1789263, baseEnd_1789263] using wordTrace_append hprefix tailTrace_1789263
  have hstable : (prefixWord ++ tailWord_1789263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789263).length < 2 ^ (prefixWord ++ tailWord_1789263).sum := by decide
  have hdescent : baseEnd_1789263 < baseStart_1789263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789314 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1789314 : Nat := 118140960795 + 1789314 * 2 ^ 59
def prefixEnd_1789314 : Nat := 4983230072969 + 3 ^ 40 * 1789314 * 2
def baseEnd_1789314 : Nat := 918778123819117534446101

theorem tailTrace_1789314 : CollatzResearch.WordTrace tailWord_1789314 prefixEnd_1789314 918778123819117534446101 := by
  unfold tailWord_1789314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315410759907110836751749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43507762026418962231337997 16315410759907110836751749)
  ·
    refine ⟨3059139517482583281890953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16315410759907110836751749 3059139517482583281890953)
    ·
      refine ⟨2294354638111937461418215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059139517482583281890953 2294354638111937461418215)
      ·
        refine ⟨3441531957167906192127323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294354638111937461418215 3441531957167906192127323)
        ·
          refine ⟨5162297935751859288190985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441531957167906192127323 5162297935751859288190985)
          ·
            refine ⟨3871723451813894466143239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162297935751859288190985 3871723451813894466143239)
            ·
              refine ⟨5807585177720841699214859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871723451813894466143239 5807585177720841699214859)
              ·
                refine ⟨8711377766581262548822289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807585177720841699214859 8711377766581262548822289)
                ·
                  refine ⟨6533533324935946911616717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711377766581262548822289 6533533324935946911616717)
                  ·
                    refine ⟨2450074996850980091856269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533533324935946911616717 2450074996850980091856269)
                    ·
                      refine ⟨918778123819117534446101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450074996850980091856269 918778123819117534446101)
                      ·
                        rfl

theorem cell23_1789314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1789314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789314 prefixEnd_1789314 := by exact prefixLift 1789314
  have htrace : WordTrace (prefixWord ++ tailWord_1789314) baseStart_1789314 baseEnd_1789314 := by
    simpa [prefixWord, tailWord_1789314, baseEnd_1789314] using wordTrace_append hprefix tailTrace_1789314
  have hstable : (prefixWord ++ tailWord_1789314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789314).length < 2 ^ (prefixWord ++ tailWord_1789314).sum := by decide
  have hdescent : baseEnd_1789314 < baseStart_1789314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789337 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_1789337 : Nat := 118140960795 + 1789337 * 2 ^ 59
def prefixEnd_1789337 : Nat := 4983230072969 + 3 ^ 40 * 1789337 * 2
def baseEnd_1789337 : Nat := 918789933874170944458495

theorem tailTrace_1789337 : CollatzResearch.WordTrace tailWord_1789337 prefixEnd_1789337 918789933874170944458495 := by
  unfold tailWord_1789337
  simp only [CollatzResearch.WordTrace]
  refine ⟨65262481918545118275094265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43508321279030078850062843 65262481918545118275094265)
  ·
    refine ⟨48946861438908838706320699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65262481918545118275094265 48946861438908838706320699)
    ·
      refine ⟨73420292158363258059481049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48946861438908838706320699 73420292158363258059481049)
      ·
        refine ⟨55065219118772443544610787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73420292158363258059481049 55065219118772443544610787)
        ·
          refine ⟨82597828678158665316916181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55065219118772443544610787 82597828678158665316916181)
          ·
            refine ⟨1935886609644343718365223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82597828678158665316916181 1935886609644343718365223)
            ·
              refine ⟨2903829914466515577547835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935886609644343718365223 2903829914466515577547835)
              ·
                refine ⟨4355744871699773366321753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903829914466515577547835 4355744871699773366321753)
                ·
                  refine ⟨3266808653774830024741315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355744871699773366321753 3266808653774830024741315)
                  ·
                    refine ⟨4900212980662245037111973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3266808653774830024741315 4900212980662245037111973)
                    ·
                      refine ⟨918789933874170944458495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4900212980662245037111973 918789933874170944458495)
                      ·
                        rfl

theorem cell23_1789337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_1789337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789337 prefixEnd_1789337 := by exact prefixLift 1789337
  have htrace : WordTrace (prefixWord ++ tailWord_1789337) baseStart_1789337 baseEnd_1789337 := by
    simpa [prefixWord, tailWord_1789337, baseEnd_1789337] using wordTrace_append hprefix tailTrace_1789337
  have hstable : (prefixWord ++ tailWord_1789337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789337).length < 2 ^ (prefixWord ++ tailWord_1789337).sum := by decide
  have hdescent : baseEnd_1789337 < baseStart_1789337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789387 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 3]
def baseStart_1789387 : Nat := 118140960795 + 1789387 * 2 ^ 59
def prefixEnd_1789387 : Nat := 4983230072969 + 3 ^ 40 * 1789387 * 2
def baseEnd_1789387 : Nat := 918815607906895748833265

theorem tailTrace_1789387 : CollatzResearch.WordTrace tailWord_1789387 prefixEnd_1789387 918815607906895748833265 := by
  unfold tailWord_1789387
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264305568363976814414415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43509537045575984542942943 65264305568363976814414415)
  ·
    refine ⟨97896458352545965221621623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65264305568363976814414415 97896458352545965221621623)
    ·
      refine ⟨146844687528818947832432435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97896458352545965221621623 146844687528818947832432435)
      ·
        refine ⟨220267031293228421748648653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146844687528818947832432435 220267031293228421748648653)
        ·
          refine ⟨82600136734960658155743245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220267031293228421748648653 82600136734960658155743245)
          ·
            refine ⟨30975051275610246808403717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82600136734960658155743245 30975051275610246808403717)
            ·
              refine ⟨5807822114176921276575697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30975051275610246808403717 5807822114176921276575697)
              ·
                refine ⟨4355866585632690957431773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807822114176921276575697 4355866585632690957431773)
                ·
                  refine ⟨1633449969612259109036915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4355866585632690957431773 1633449969612259109036915)
                  ·
                    refine ⟨2450174954418388663555373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633449969612259109036915 2450174954418388663555373)
                    ·
                      refine ⟨918815607906895748833265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450174954418388663555373 918815607906895748833265)
                      ·
                        rfl

theorem cell23_1789387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 3].length) (baseStart_1789387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789387 prefixEnd_1789387 := by exact prefixLift 1789387
  have htrace : WordTrace (prefixWord ++ tailWord_1789387) baseStart_1789387 baseEnd_1789387 := by
    simpa [prefixWord, tailWord_1789387, baseEnd_1789387] using wordTrace_append hprefix tailTrace_1789387
  have hstable : (prefixWord ++ tailWord_1789387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789387).length < 2 ^ (prefixWord ++ tailWord_1789387).sum := by decide
  have hdescent : baseEnd_1789387 < baseStart_1789387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789390 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1789390 : Nat := 118140960795 + 1789390 * 2 ^ 59
def prefixEnd_1789390 : Nat := 4983230072969 + 3 ^ 40 * 1789390 * 2
def baseEnd_1789390 : Nat := 306272382782953079031917

theorem tailTrace_1789390 : CollatzResearch.WordTrace tailWord_1789390 prefixEnd_1789390 306272382782953079031917 := by
  unfold tailWord_1789390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158051873419138540846703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43509609991568738884515749 8158051873419138540846703)
  ·
    refine ⟨12237077810128707811270055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8158051873419138540846703 12237077810128707811270055)
    ·
      refine ⟨18355616715193061716905083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12237077810128707811270055 18355616715193061716905083)
      ·
        refine ⟨27533425072789592575357625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18355616715193061716905083 27533425072789592575357625)
        ·
          refine ⟨20650068804592194431518219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27533425072789592575357625 20650068804592194431518219)
          ·
            refine ⟨30975103206888291647277329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20650068804592194431518219 30975103206888291647277329)
            ·
              refine ⟨23231327405166218735457997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30975103206888291647277329 23231327405166218735457997)
              ·
                refine ⟨8711747776937332025796749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23231327405166218735457997 8711747776937332025796749)
                ·
                  refine ⟨3266905416351499509673781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8711747776937332025796749 3266905416351499509673781)
                  ·
                    refine ⟨306272382782953079031917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3266905416351499509673781 306272382782953079031917)
                    ·
                      rfl

theorem cell23_1789390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1789390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789390 prefixEnd_1789390 := by exact prefixLift 1789390
  have htrace : WordTrace (prefixWord ++ tailWord_1789390) baseStart_1789390 baseEnd_1789390 := by
    simpa [prefixWord, tailWord_1789390, baseEnd_1789390] using wordTrace_append hprefix tailTrace_1789390
  have hstable : (prefixWord ++ tailWord_1789390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789390).length < 2 ^ (prefixWord ++ tailWord_1789390).sum := by decide
  have hdescent : baseEnd_1789390 < baseStart_1789390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789397 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1789397 : Nat := 118140960795 + 1789397 * 2 ^ 59
def prefixEnd_1789397 : Nat := 4983230072969 + 3 ^ 40 * 1789397 * 2
def baseEnd_1789397 : Nat := 918820742713440709708219

theorem tailTrace_1789397 : CollatzResearch.WordTrace tailWord_1789397 prefixEnd_1789397 918820742713440709708219 := by
  unfold tailWord_1789397
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264670298327748522278445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43509780198885165681518963 65264670298327748522278445)
  ·
    refine ⟨24474251361872905695854417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65264670298327748522278445 24474251361872905695854417)
    ·
      refine ⟨18355688521404679271890813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24474251361872905695854417 18355688521404679271890813)
      ·
        refine ⟨6883383195526754726959055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18355688521404679271890813 6883383195526754726959055)
        ·
          refine ⟨10325074793290132090438583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883383195526754726959055 10325074793290132090438583)
          ·
            refine ⟨15487612189935198135657875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325074793290132090438583 15487612189935198135657875)
            ·
              refine ⟨23231418284902797203486813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15487612189935198135657875 23231418284902797203486813)
              ·
                refine ⟨8711781856838548951307555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23231418284902797203486813 8711781856838548951307555)
                ·
                  refine ⟨13067672785257823426961333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711781856838548951307555 13067672785257823426961333)
                  ·
                    refine ⟨1225094323617920946277625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13067672785257823426961333 1225094323617920946277625)
                    ·
                      refine ⟨918820742713440709708219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225094323617920946277625 918820742713440709708219)
                      ·
                        rfl

theorem cell23_1789397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1789397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789397 prefixEnd_1789397 := by exact prefixLift 1789397
  have htrace : WordTrace (prefixWord ++ tailWord_1789397) baseStart_1789397 baseEnd_1789397 := by
    simpa [prefixWord, tailWord_1789397, baseEnd_1789397] using wordTrace_append hprefix tailTrace_1789397
  have hstable : (prefixWord ++ tailWord_1789397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789397).length < 2 ^ (prefixWord ++ tailWord_1789397).sum := by decide
  have hdescent : baseEnd_1789397 < baseStart_1789397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789398 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1789398 : Nat := 118140960795 + 1789398 * 2 ^ 59
def prefixEnd_1789398 : Nat := 4983230072969 + 3 ^ 40 * 1789398 * 2
def baseEnd_1789398 : Nat := 306273752064698401931905

theorem tailTrace_1789398 : CollatzResearch.WordTrace tailWord_1789398 prefixEnd_1789398 306273752064698401931905 := by
  unfold tailWord_1789398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079044173207757855816553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43509804514216083795376565 4079044173207757855816553)
  ·
    refine ⟨3059283129905818391862415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079044173207757855816553 3059283129905818391862415)
    ·
      refine ⟨4588924694858727587793623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059283129905818391862415 4588924694858727587793623)
      ·
        refine ⟨6883387042288091381690435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588924694858727587793623 6883387042288091381690435)
        ·
          refine ⟨10325080563432137072535653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883387042288091381690435 10325080563432137072535653)
          ·
            refine ⟨1935952605643525701100435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10325080563432137072535653 1935952605643525701100435)
            ·
              refine ⟨2903928908465288551650653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935952605643525701100435 2903928908465288551650653)
              ·
                refine ⟨1088973340674483206868995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2903928908465288551650653 1088973340674483206868995)
                ·
                  refine ⟨1633460011011724810303493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088973340674483206868995 1633460011011724810303493)
                  ·
                    refine ⟨306273752064698401931905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633460011011724810303493 306273752064698401931905)
                    ·
                      rfl

theorem cell23_1789398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1789398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789398 prefixEnd_1789398 := by exact prefixLift 1789398
  have htrace : WordTrace (prefixWord ++ tailWord_1789398) baseStart_1789398 baseEnd_1789398 := by
    simpa [prefixWord, tailWord_1789398, baseEnd_1789398] using wordTrace_append hprefix tailTrace_1789398
  have hstable : (prefixWord ++ tailWord_1789398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789398).length < 2 ^ (prefixWord ++ tailWord_1789398).sum := by decide
  have hdescent : baseEnd_1789398 < baseStart_1789398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789441 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1789441 : Nat := 118140960795 + 1789441 * 2 ^ 59
def prefixEnd_1789441 : Nat := 4983230072969 + 3 ^ 40 * 1789441 * 2
def baseEnd_1789441 : Nat := 306281111954079512519339

theorem tailTrace_1789441 : CollatzResearch.WordTrace tailWord_1789441 prefixEnd_1789441 306281111954079512519339 := by
  unfold tailWord_1789441
  simp only [CollatzResearch.WordTrace]
  refine ⟨65266275110168344036880177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43510850073445562691253451 65266275110168344036880177)
  ·
    refine ⟨48949706332626258027660133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65266275110168344036880177 48949706332626258027660133)
    ·
      refine ⟨9178069937367423380186275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48949706332626258027660133 9178069937367423380186275)
      ·
        refine ⟨13767104906051135070279413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178069937367423380186275 13767104906051135070279413)
        ·
          refine ⟨1290666084942293912838695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13767104906051135070279413 1290666084942293912838695)
          ·
            refine ⟨1935999127413440869258043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290666084942293912838695 1935999127413440869258043)
            ·
              refine ⟨2903998691120161303887065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935999127413440869258043 2903998691120161303887065)
              ·
                refine ⟨2177999018340120977915299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903998691120161303887065 2177999018340120977915299)
                ·
                  refine ⟨3266998527510181466872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177999018340120977915299 3266998527510181466872949)
                  ·
                    refine ⟨306281111954079512519339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3266998527510181466872949 306281111954079512519339)
                    ·
                      rfl

theorem cell23_1789441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1789441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789441 prefixEnd_1789441 := by exact prefixLift 1789441
  have htrace : WordTrace (prefixWord ++ tailWord_1789441) baseStart_1789441 baseEnd_1789441 := by
    simpa [prefixWord, tailWord_1789441, baseEnd_1789441] using wordTrace_append hprefix tailTrace_1789441
  have hstable : (prefixWord ++ tailWord_1789441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789441).length < 2 ^ (prefixWord ++ tailWord_1789441).sum := by decide
  have hdescent : baseEnd_1789441 < baseStart_1789441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789444 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1789444 : Nat := 118140960795 + 1789444 * 2 ^ 59
def prefixEnd_1789444 : Nat := 4983230072969 + 3 ^ 40 * 1789444 * 2
def baseEnd_1789444 : Nat := 918844876304202025820503

theorem tailTrace_1789444 : CollatzResearch.WordTrace tailWord_1789444 prefixEnd_1789444 918844876304202025820503 := by
  unfold tailWord_1789444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32633192264578737774619693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43510923019438317032826257 32633192264578737774619693)
  ·
    refine ⟨12237447099217026665482385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32633192264578737774619693 12237447099217026665482385)
    ·
      refine ⟨9178085324412769999111789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12237447099217026665482385 9178085324412769999111789)
      ·
        refine ⟨3441781996654788749666921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9178085324412769999111789 3441781996654788749666921)
        ·
          refine ⟨2581336497491091562250191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441781996654788749666921 2581336497491091562250191)
          ·
            refine ⟨3872004746236637343375287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581336497491091562250191 3872004746236637343375287)
            ·
              refine ⟨5808007119354956015062931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872004746236637343375287 5808007119354956015062931)
              ·
                refine ⟨8712010679032434022594397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808007119354956015062931 8712010679032434022594397)
                ·
                  refine ⟨3267004004637162758472899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8712010679032434022594397 3267004004637162758472899)
                  ·
                    refine ⟨4900506006955744137709349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267004004637162758472899 4900506006955744137709349)
                    ·
                      refine ⟨918844876304202025820503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4900506006955744137709349 918844876304202025820503)
                      ·
                        rfl

theorem cell23_1789444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1789444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789444 prefixEnd_1789444 := by exact prefixLift 1789444
  have htrace : WordTrace (prefixWord ++ tailWord_1789444) baseStart_1789444 baseEnd_1789444 := by
    simpa [prefixWord, tailWord_1789444, baseEnd_1789444] using wordTrace_append hprefix tailTrace_1789444
  have hstable : (prefixWord ++ tailWord_1789444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789444).length < 2 ^ (prefixWord ++ tailWord_1789444).sum := by decide
  have hdescent : baseEnd_1789444 < baseStart_1789444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789450 : List Nat := [3, 1, 2, 2, 2, 2, 2, 9]
def baseStart_1789450 : Nat := 118140960795 + 1789450 * 2 ^ 59
def prefixEnd_1789450 : Nat := 4983230072969 + 3 ^ 40 * 1789450 * 2
def baseEnd_1789450 : Nat := 34031405821782555642425

theorem tailTrace_1789450 : CollatzResearch.WordTrace tailWord_1789450 prefixEnd_1789450 34031405821782555642425 := by
  unfold tailWord_1789450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316650841783934643489451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43511068911423825715971869 16316650841783934643489451)
  ·
    refine ⟨24474976262675901965234177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16316650841783934643489451 24474976262675901965234177)
    ·
      refine ⟨18356232197006926473925633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24474976262675901965234177 18356232197006926473925633)
      ·
        refine ⟨13767174147755194855444225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18356232197006926473925633 13767174147755194855444225)
        ·
          refine ⟨10325380610816396141583169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13767174147755194855444225 10325380610816396141583169)
          ·
            refine ⟨7744035458112297106187377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10325380610816396141583169 7744035458112297106187377)
            ·
              refine ⟨5808026593584222829640533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7744035458112297106187377 5808026593584222829640533)
              ·
                refine ⟨34031405821782555642425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5808026593584222829640533 34031405821782555642425)
                ·
                  rfl

theorem cell23_1789450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_1789450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789450 prefixEnd_1789450 := by exact prefixLift 1789450
  have htrace : WordTrace (prefixWord ++ tailWord_1789450) baseStart_1789450 baseEnd_1789450 := by
    simpa [prefixWord, tailWord_1789450, baseEnd_1789450] using wordTrace_append hprefix tailTrace_1789450
  have hstable : (prefixWord ++ tailWord_1789450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789450).length < 2 ^ (prefixWord ++ tailWord_1789450).sum := by decide
  have hdescent : baseEnd_1789450 < baseStart_1789450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789464 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1789464 : Nat := 118140960795 + 1789464 * 2 ^ 59
def prefixEnd_1789464 : Nat := 4983230072969 + 3 ^ 40 * 1789464 * 2
def baseEnd_1789464 : Nat := 918855145917291947570411

theorem tailTrace_1789464 : CollatzResearch.WordTrace tailWord_1789464 prefixEnd_1789464 918855145917291947570411 := by
  unfold tailWord_1789464
  simp only [CollatzResearch.WordTrace]
  refine ⟨32633556994542509482483723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43511409326056679309978297 32633556994542509482483723)
  ·
    refine ⟨48950335491813764223725585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32633556994542509482483723 48950335491813764223725585)
    ·
      refine ⟨36712751618860323167794189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48950335491813764223725585 36712751618860323167794189)
      ·
        refine ⟨13767281857072621187922821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36712751618860323167794189 13767281857072621187922821)
        ·
          refine ⟨2581365348201116472735529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13767281857072621187922821 2581365348201116472735529)
          ·
            refine ⟨1936024011150837354551647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581365348201116472735529 1936024011150837354551647)
            ·
              refine ⟨2904036016726256031827471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936024011150837354551647 2904036016726256031827471)
              ·
                refine ⟨4356054025089384047741207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904036016726256031827471 4356054025089384047741207)
                ·
                  refine ⟨6534081037634076071611811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356054025089384047741207 6534081037634076071611811)
                  ·
                    refine ⟨9801121556451114107417717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6534081037634076071611811 9801121556451114107417717)
                    ·
                      refine ⟨918855145917291947570411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9801121556451114107417717 918855145917291947570411)
                      ·
                        rfl

theorem cell23_1789464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1789464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789464 prefixEnd_1789464 := by exact prefixLift 1789464
  have htrace : WordTrace (prefixWord ++ tailWord_1789464) baseStart_1789464 baseEnd_1789464 := by
    simpa [prefixWord, tailWord_1789464, baseEnd_1789464] using wordTrace_append hprefix tailTrace_1789464
  have hstable : (prefixWord ++ tailWord_1789464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789464).length < 2 ^ (prefixWord ++ tailWord_1789464).sum := by decide
  have hdescent : baseEnd_1789464 < baseStart_1789464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789490 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1789490 : Nat := 118140960795 + 1789490 * 2 ^ 59
def prefixEnd_1789490 : Nat := 4983230072969 + 3 ^ 40 * 1789490 * 2
def baseEnd_1789490 : Nat := 918868496414308845845291

theorem tailTrace_1789490 : CollatzResearch.WordTrace tailWord_1789490 prefixEnd_1789490 918868496414308845845291 := by
  unfold tailWord_1789490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317015571747706351353481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43512041524660550270275949 16317015571747706351353481)
  ·
    refine ⟨12237761678810779763515111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16317015571747706351353481 12237761678810779763515111)
    ·
      refine ⟨18356642518216169645272667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12237761678810779763515111 18356642518216169645272667)
      ·
        refine ⟨27534963777324254467909001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18356642518216169645272667 27534963777324254467909001)
        ·
          refine ⟨20651222832993190850931751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27534963777324254467909001 20651222832993190850931751)
          ·
            refine ⟨30976834249489786276397627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20651222832993190850931751 30976834249489786276397627)
            ·
              refine ⟨46465251374234679414596441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30976834249489786276397627 46465251374234679414596441)
              ·
                refine ⟨34848938530676009560947331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46465251374234679414596441 34848938530676009560947331)
                ·
                  refine ⟨52273407796014014341420997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34848938530676009560947331 52273407796014014341420997)
                  ·
                    refine ⟨9801263961752627689016437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52273407796014014341420997 9801263961752627689016437)
                    ·
                      refine ⟨918868496414308845845291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9801263961752627689016437 918868496414308845845291)
                      ·
                        rfl

theorem cell23_1789490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1789490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789490 prefixEnd_1789490 := by exact prefixLift 1789490
  have htrace : WordTrace (prefixWord ++ tailWord_1789490) baseStart_1789490 baseEnd_1789490 := by
    simpa [prefixWord, tailWord_1789490, baseEnd_1789490] using wordTrace_append hprefix tailTrace_1789490
  have hstable : (prefixWord ++ tailWord_1789490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789490).length < 2 ^ (prefixWord ++ tailWord_1789490).sum := by decide
  have hdescent : baseEnd_1789490 < baseStart_1789490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789504 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2]
def baseStart_1789504 : Nat := 118140960795 + 1789504 * 2 ^ 59
def prefixEnd_1789504 : Nat := 4983230072969 + 3 ^ 40 * 1789504 * 2
def baseEnd_1789504 : Nat := 918875685143471791070227

theorem tailTrace_1789504 : CollatzResearch.WordTrace tailWord_1789504 prefixEnd_1789504 918875685143471791070227 := by
  unfold tailWord_1789504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32634286454470052898211783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43512381939293403864282377 32634286454470052898211783)
  ·
    refine ⟨48951429681705079347317675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32634286454470052898211783 48951429681705079347317675)
    ·
      refine ⟨73427144522557619020976513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48951429681705079347317675 73427144522557619020976513)
      ·
        refine ⟨55070358391918214265732385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73427144522557619020976513 55070358391918214265732385)
        ·
          refine ⟨41302768793938660699299289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55070358391918214265732385 41302768793938660699299289)
          ·
            refine ⟨30977076595453995524474467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41302768793938660699299289 30977076595453995524474467)
            ·
              refine ⟨46465614893180993286711701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30977076595453995524474467 46465614893180993286711701)
              ·
                refine ⟨2178075698117859060314611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46465614893180993286711701 2178075698117859060314611)
                ·
                  refine ⟨3267113547176788590471917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178075698117859060314611 3267113547176788590471917)
                  ·
                    refine ⟨1225167580191295721426969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267113547176788590471917 1225167580191295721426969)
                    ·
                      refine ⟨918875685143471791070227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225167580191295721426969 918875685143471791070227)
                      ·
                        rfl

theorem cell23_1789504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_1789504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789504 prefixEnd_1789504 := by exact prefixLift 1789504
  have htrace : WordTrace (prefixWord ++ tailWord_1789504) baseStart_1789504 baseEnd_1789504 := by
    simpa [prefixWord, tailWord_1789504, baseEnd_1789504] using wordTrace_append hprefix tailTrace_1789504
  have hstable : (prefixWord ++ tailWord_1789504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789504).length < 2 ^ (prefixWord ++ tailWord_1789504).sum := by decide
  have hdescent : baseEnd_1789504 < baseStart_1789504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789520 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1789520 : Nat := 118140960795 + 1789520 * 2 ^ 59
def prefixEnd_1789520 : Nat := 4983230072969 + 3 ^ 40 * 1789520 * 2
def baseEnd_1789520 : Nat := 918883900833943728470153

theorem tailTrace_1789520 : CollatzResearch.WordTrace tailWord_1789520 prefixEnd_1789520 918883900833943728470153 := by
  unfold tailWord_1789520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32634578238441070264503007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43512770984588093686004009 32634578238441070264503007)
  ·
    refine ⟨48951867357661605396754511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32634578238441070264503007 48951867357661605396754511)
    ·
      refine ⟨73427801036492408095131767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48951867357661605396754511 73427801036492408095131767)
      ·
        refine ⟨110141701554738612142697651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73427801036492408095131767 110141701554738612142697651)
        ·
          refine ⟨165212552332107918214046477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110141701554738612142697651 165212552332107918214046477)
          ·
            refine ⟨61954707124540469330267429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165212552332107918214046477 61954707124540469330267429)
            ·
              refine ⟨11616507585851337999425143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61954707124540469330267429 11616507585851337999425143)
              ·
                refine ⟨17424761378777006999137715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11616507585851337999425143 17424761378777006999137715)
                ·
                  refine ⟨26137142068165510498706573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17424761378777006999137715 26137142068165510498706573)
                  ·
                    refine ⟨9801428275562066437014965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26137142068165510498706573 9801428275562066437014965)
                    ·
                      refine ⟨918883900833943728470153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9801428275562066437014965 918883900833943728470153)
                      ·
                        rfl

theorem cell23_1789520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1789520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789520 prefixEnd_1789520 := by exact prefixLift 1789520
  have htrace : WordTrace (prefixWord ++ tailWord_1789520) baseStart_1789520 baseEnd_1789520 := by
    simpa [prefixWord, tailWord_1789520, baseEnd_1789520] using wordTrace_append hprefix tailTrace_1789520
  have hstable : (prefixWord ++ tailWord_1789520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789520).length < 2 ^ (prefixWord ++ tailWord_1789520).sum := by decide
  have hdescent : baseEnd_1789520 < baseStart_1789520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789591 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 5]
def baseStart_1789591 : Nat := 118140960795 + 1789591 * 2 ^ 59
def prefixEnd_1789591 : Nat := 4983230072969 + 3 ^ 40 * 1789591 * 2
def baseEnd_1789591 : Nat := 102102261995601438964703

theorem tailTrace_1789591 : CollatzResearch.WordTrace tailWord_1789591 prefixEnd_1789591 102102261995601438964703 := by
  unfold tailWord_1789591
  simp only [CollatzResearch.WordTrace]
  refine ⟨65271746059624919654840627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43514497373083279769893751 65271746059624919654840627)
  ·
    refine ⟨97907619089437379482260941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65271746059624919654840627 97907619089437379482260941)
    ·
      refine ⟨36715357158539017305847853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97907619089437379482260941 36715357158539017305847853)
      ·
        refine ⟨13768258934452131489692945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36715357158539017305847853 13768258934452131489692945)
        ·
          refine ⟨10326194200839098617269709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13768258934452131489692945 10326194200839098617269709)
          ·
            refine ⟨3872322825314661981476141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10326194200839098617269709 3872322825314661981476141)
            ·
              refine ⟨1452121059492998243053553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3872322825314661981476141 1452121059492998243053553)
              ·
                refine ⟨1089090794619748682290165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452121059492998243053553 1089090794619748682290165)
                ·
                  refine ⟨102102261995601438964703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089090794619748682290165 102102261995601438964703)
                  ·
                    rfl

theorem cell23_1789591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 5].length) (baseStart_1789591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789591 prefixEnd_1789591 := by exact prefixLift 1789591
  have htrace : WordTrace (prefixWord ++ tailWord_1789591) baseStart_1789591 baseEnd_1789591 := by
    simpa [prefixWord, tailWord_1789591, baseEnd_1789591] using wordTrace_append hprefix tailTrace_1789591
  have hstable : (prefixWord ++ tailWord_1789591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789591).length < 2 ^ (prefixWord ++ tailWord_1789591).sum := by decide
  have hdescent : baseEnd_1789591 < baseStart_1789591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789621 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1789621 : Nat := 118140960795 + 1789621 * 2 ^ 59
def prefixEnd_1789621 : Nat := 4983230072969 + 3 ^ 40 * 1789621 * 2
def baseEnd_1789621 : Nat := 306311920793349277769063

theorem tailTrace_1789621 : CollatzResearch.WordTrace tailWord_1789621 prefixEnd_1789621 306311920793349277769063 := by
  unfold tailWord_1789621
  simp only [CollatzResearch.WordTrace]
  refine ⟨65272840249516234778432717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43515226833010823185621811 65272840249516234778432717)
  ·
    refine ⟨24477315093568588041912269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65272840249516234778432717 24477315093568588041912269)
    ·
      refine ⟨9178993160088220515717101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24477315093568588041912269 9178993160088220515717101)
      ·
        refine ⟨3442122435033082693393913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9178993160088220515717101 3442122435033082693393913)
        ·
          refine ⟨2581591826274812020045435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442122435033082693393913 2581591826274812020045435)
          ·
            refine ⟨3872387739412218030068153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581591826274812020045435 3872387739412218030068153)
            ·
              refine ⟨2904290804559163522551115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872387739412218030068153 2904290804559163522551115)
              ·
                refine ⟨4356436206838745283826673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904290804559163522551115 4356436206838745283826673)
                ·
                  refine ⟨3267327155129058962870005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356436206838745283826673 3267327155129058962870005)
                  ·
                    refine ⟨306311920793349277769063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3267327155129058962870005 306311920793349277769063)
                    ·
                      rfl

theorem cell23_1789621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1789621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789621 prefixEnd_1789621 := by exact prefixLift 1789621
  have htrace : WordTrace (prefixWord ++ tailWord_1789621) baseStart_1789621 baseEnd_1789621 := by
    simpa [prefixWord, tailWord_1789621, baseEnd_1789621] using wordTrace_append hprefix tailTrace_1789621
  have hstable : (prefixWord ++ tailWord_1789621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789621).length < 2 ^ (prefixWord ++ tailWord_1789621).sum := by decide
  have hdescent : baseEnd_1789621 < baseStart_1789621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789627 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3]
def baseStart_1789627 : Nat := 118140960795 + 1789627 * 2 ^ 59
def prefixEnd_1789627 : Nat := 4983230072969 + 3 ^ 40 * 1789627 * 2
def baseEnd_1789627 : Nat := 918938843263974809832161

theorem tailTrace_1789627 : CollatzResearch.WordTrace tailWord_1789627 prefixEnd_1789627 918938843263974809832161 := by
  unfold tailWord_1789627
  simp only [CollatzResearch.WordTrace]
  refine ⟨65273059087494497803151135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43515372724996331868767423 65273059087494497803151135)
  ·
    refine ⟨97909588631241746704726703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65273059087494497803151135 97909588631241746704726703)
    ·
      refine ⟨146864382946862620057090055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97909588631241746704726703 146864382946862620057090055)
      ·
        refine ⟨220296574420293930085635083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146864382946862620057090055 220296574420293930085635083)
        ·
          refine ⟨330444861630440895128452625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220296574420293930085635083 330444861630440895128452625)
          ·
            refine ⟨247833646222830671346339469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330444861630440895128452625 247833646222830671346339469)
            ·
              refine ⟨92937617333561501754877301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247833646222830671346339469 92937617333561501754877301)
              ·
                refine ⟨8712901625021390789519747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92937617333561501754877301 8712901625021390789519747)
                ·
                  refine ⟨13069352437532086184279621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712901625021390789519747 13069352437532086184279621)
                  ·
                    refine ⟨2450503582037266159552429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13069352437532086184279621 2450503582037266159552429)
                    ·
                      refine ⟨918938843263974809832161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450503582037266159552429 918938843263974809832161)
                      ·
                        rfl

theorem cell23_1789627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].length) (baseStart_1789627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789627 prefixEnd_1789627 := by exact prefixLift 1789627
  have htrace : WordTrace (prefixWord ++ tailWord_1789627) baseStart_1789627 baseEnd_1789627 := by
    simpa [prefixWord, tailWord_1789627, baseEnd_1789627] using wordTrace_append hprefix tailTrace_1789627
  have hstable : (prefixWord ++ tailWord_1789627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789627).length < 2 ^ (prefixWord ++ tailWord_1789627).sum := by decide
  have hdescent : baseEnd_1789627 < baseStart_1789627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789638 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1789638 : Nat := 118140960795 + 1789638 * 2 ^ 59
def prefixEnd_1789638 : Nat := 4983230072969 + 3 ^ 40 * 1789638 * 2
def baseEnd_1789638 : Nat := 306314830517058088931537

theorem tailTrace_1789638 : CollatzResearch.WordTrace tailWord_1789638 prefixEnd_1789638 306314830517058088931537 := by
  unfold tailWord_1789638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039795634076707708806299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43515640193636431121201045 2039795634076707708806299)
  ·
    refine ⟨3059693451115061563209449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039795634076707708806299 3059693451115061563209449)
    ·
      refine ⟨2294770088336296172407087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059693451115061563209449 2294770088336296172407087)
      ·
        refine ⟨3442155132504444258610631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294770088336296172407087 3442155132504444258610631)
        ·
          refine ⟨5163232698756666387915947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442155132504444258610631 5163232698756666387915947)
          ·
            refine ⟨7744849048134999581873921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163232698756666387915947 7744849048134999581873921)
            ·
              refine ⟨5808636786101249686405441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7744849048134999581873921 5808636786101249686405441)
              ·
                refine ⟨4356477589575937264804081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808636786101249686405441 4356477589575937264804081)
                ·
                  refine ⟨3267358192181952948603061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356477589575937264804081 3267358192181952948603061)
                  ·
                    refine ⟨306314830517058088931537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3267358192181952948603061 306314830517058088931537)
                    ·
                      rfl

theorem cell23_1789638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1789638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789638 prefixEnd_1789638 := by exact prefixLift 1789638
  have htrace : WordTrace (prefixWord ++ tailWord_1789638) baseStart_1789638 baseEnd_1789638 := by
    simpa [prefixWord, tailWord_1789638, baseEnd_1789638] using wordTrace_append hprefix tailTrace_1789638
  have hstable : (prefixWord ++ tailWord_1789638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789638).length < 2 ^ (prefixWord ++ tailWord_1789638).sum := by decide
  have hdescent : baseEnd_1789638 < baseStart_1789638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789707 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 6]
def baseStart_1789707 : Nat := 118140960795 + 1789707 * 2 ^ 59
def prefixEnd_1789707 : Nat := 4983230072969 + 3 ^ 40 * 1789707 * 2
def baseEnd_1789707 : Nat := 306326640572111498943931

theorem tailTrace_1789707 : CollatzResearch.WordTrace tailWord_1789707 prefixEnd_1789707 306326640572111498943931 := by
  unfold tailWord_1789707
  simp only [CollatzResearch.WordTrace]
  refine ⟨65275976927204671466063375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43517317951469780977375583 65275976927204671466063375)
  ·
    refine ⟨97913965390807007199095063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65275976927204671466063375 97913965390807007199095063)
    ·
      refine ⟨146870948086210510798642595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97913965390807007199095063 146870948086210510798642595)
      ·
        refine ⟨220306422129315766197963893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146870948086210510798642595 220306422129315766197963893)
        ·
          refine ⟨20653727074623353081059115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220306422129315766197963893 20653727074623353081059115)
          ·
            refine ⟨30980590611935029621588673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653727074623353081059115 30980590611935029621588673)
            ·
              refine ⟨23235442958951272216191505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30980590611935029621588673 23235442958951272216191505)
              ·
                refine ⟨17426582219213454162143629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23235442958951272216191505 17426582219213454162143629)
                ·
                  refine ⟨6534968332205045310803861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17426582219213454162143629 6534968332205045310803861)
                  ·
                    refine ⟨306326640572111498943931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6534968332205045310803861 306326640572111498943931)
                    ·
                      rfl

theorem cell23_1789707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_1789707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789707 prefixEnd_1789707 := by exact prefixLift 1789707
  have htrace : WordTrace (prefixWord ++ tailWord_1789707) baseStart_1789707 baseEnd_1789707 := by
    simpa [prefixWord, tailWord_1789707, baseEnd_1789707] using wordTrace_append hprefix tailTrace_1789707
  have hstable : (prefixWord ++ tailWord_1789707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789707).length < 2 ^ (prefixWord ++ tailWord_1789707).sum := by decide
  have hdescent : baseEnd_1789707 < baseStart_1789707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789708 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_1789708 : Nat := 118140960795 + 1789708 * 2 ^ 59
def prefixEnd_1789708 : Nat := 4983230072969 + 3 ^ 40 * 1789708 * 2
def baseEnd_1789708 : Nat := 918980435196988992919289

theorem tailTrace_1789708 : CollatzResearch.WordTrace tailWord_1789708 prefixEnd_1789708 918980435196988992919289 := by
  unfold tailWord_1789708
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638006700100524318424889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43517342266800699091233185 32638006700100524318424889)
  ·
    refine ⟨24478505025075393238818667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32638006700100524318424889 24478505025075393238818667)
    ·
      refine ⟨36717757537613089858228001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478505025075393238818667 36717757537613089858228001)
      ·
        refine ⟨27538318153209817393671001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36717757537613089858228001 27538318153209817393671001)
        ·
          refine ⟨20653738614907363045253251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27538318153209817393671001 20653738614907363045253251)
          ·
            refine ⟨30980607922361044567879877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653738614907363045253251 30980607922361044567879877)
            ·
              refine ⟨5808863985442695856477477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30980607922361044567879877 5808863985442695856477477)
              ·
                refine ⟨1089161997270505473089527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5808863985442695856477477 1089161997270505473089527)
                ·
                  refine ⟨1633742995905758209634291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089161997270505473089527 1633742995905758209634291)
                  ·
                    refine ⟨2450614493858637314451437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633742995905758209634291 2450614493858637314451437)
                    ·
                      refine ⟨918980435196988992919289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450614493858637314451437 918980435196988992919289)
                      ·
                        rfl

theorem cell23_1789708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_1789708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789708 prefixEnd_1789708 := by exact prefixLift 1789708
  have htrace : WordTrace (prefixWord ++ tailWord_1789708) baseStart_1789708 baseEnd_1789708 := by
    simpa [prefixWord, tailWord_1789708, baseEnd_1789708] using wordTrace_append hprefix tailTrace_1789708
  have hstable : (prefixWord ++ tailWord_1789708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789708).length < 2 ^ (prefixWord ++ tailWord_1789708).sum := by decide
  have hdescent : baseEnd_1789708 < baseStart_1789708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789748 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1789748 : Nat := 118140960795 + 1789748 * 2 ^ 59
def prefixEnd_1789748 : Nat := 4983230072969 + 3 ^ 40 * 1789748 * 2
def baseEnd_1789748 : Nat := 919000974423168836419105

theorem tailTrace_1789748 : CollatzResearch.WordTrace tailWord_1789748 prefixEnd_1789748 919000974423168836419105 := by
  unfold tailWord_1789748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638736160028067734152949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43518314880037423645537265 32638736160028067734152949)
  ·
    refine ⟨3059881515002631350076839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32638736160028067734152949 3059881515002631350076839)
    ·
      refine ⟨4589822272503947025115259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059881515002631350076839 4589822272503947025115259)
      ·
        refine ⟨6884733408755920537672889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589822272503947025115259 6884733408755920537672889)
        ·
          refine ⟨5163550056566940403254667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884733408755920537672889 5163550056566940403254667)
          ·
            refine ⟨7745325084850410604882001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163550056566940403254667 7745325084850410604882001)
            ·
              refine ⟨5808993813637807953661501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7745325084850410604882001 5808993813637807953661501)
              ·
                refine ⟨2178372680114177982623063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808993813637807953661501 2178372680114177982623063)
                ·
                  refine ⟨3267559020171266973934595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178372680114177982623063 3267559020171266973934595)
                  ·
                    refine ⟨4901338530256900460901893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267559020171266973934595 4901338530256900460901893)
                    ·
                      refine ⟨919000974423168836419105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4901338530256900460901893 919000974423168836419105)
                      ·
                        rfl

theorem cell23_1789748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1789748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789748 prefixEnd_1789748 := by exact prefixLift 1789748
  have htrace : WordTrace (prefixWord ++ tailWord_1789748) baseStart_1789748 baseEnd_1789748 := by
    simpa [prefixWord, tailWord_1789748, baseEnd_1789748] using wordTrace_append hprefix tailTrace_1789748
  have hstable : (prefixWord ++ tailWord_1789748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789748).length < 2 ^ (prefixWord ++ tailWord_1789748).sum := by decide
  have hdescent : baseEnd_1789748 < baseStart_1789748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789754 : List Nat := [3, 1, 1, 1, 5, 3, 9]
def baseStart_1789754 : Nat := 118140960795 + 1789754 * 2 ^ 59
def prefixEnd_1789754 : Nat := 4983230072969 + 3 ^ 40 * 1789754 * 2
def baseEnd_1789754 : Nat := 11345729077865380406717

theorem tailTrace_1789754 : CollatzResearch.WordTrace tailWord_1789754 prefixEnd_1789754 11345729077865380406717 := by
  unfold tailWord_1789754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319422789508599623256079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43518460772022932328682877 16319422789508599623256079)
  ·
    refine ⟨24479134184262899434884119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319422789508599623256079 24479134184262899434884119)
    ·
      refine ⟨36718701276394349152326179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24479134184262899434884119 36718701276394349152326179)
      ·
        refine ⟨55078051914591523728489269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36718701276394349152326179 55078051914591523728489269)
        ·
          refine ⟨5163567366992955349545869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55078051914591523728489269 5163567366992955349545869)
          ·
            refine ⟨1936337762622358256079701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5163567366992955349545869 1936337762622358256079701)
            ·
              refine ⟨11345729077865380406717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1936337762622358256079701 11345729077865380406717)
              ·
                rfl

theorem cell23_1789754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 9].length) (baseStart_1789754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789754 prefixEnd_1789754 := by exact prefixLift 1789754
  have htrace : WordTrace (prefixWord ++ tailWord_1789754) baseStart_1789754 baseEnd_1789754 := by
    simpa [prefixWord, tailWord_1789754, baseEnd_1789754] using wordTrace_append hprefix tailTrace_1789754
  have hstable : (prefixWord ++ tailWord_1789754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789754).length < 2 ^ (prefixWord ++ tailWord_1789754).sum := by decide
  have hdescent : baseEnd_1789754 < baseStart_1789754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789802 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1789802 : Nat := 118140960795 + 1789802 * 2 ^ 59
def prefixEnd_1789802 : Nat := 4983230072969 + 3 ^ 40 * 1789802 * 2
def baseEnd_1789802 : Nat := 919028702378511625143857

theorem tailTrace_1789802 : CollatzResearch.WordTrace tailWord_1789802 prefixEnd_1789802 919028702378511625143857 := by
  unfold tailWord_1789802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319860465465125672692915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43519627907907001793847773 16319860465465125672692915)
  ·
    refine ⟨24479790698197688509039373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319860465465125672692915 24479790698197688509039373)
    ·
      refine ⟨9179921511824133190889765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24479790698197688509039373 9179921511824133190889765)
      ·
        refine ⟨1721235283467024973291831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9179921511824133190889765 1721235283467024973291831)
        ·
          refine ⟨2581852925200537459937747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721235283467024973291831 2581852925200537459937747)
          ·
            refine ⟨3872779387800806189906621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581852925200537459937747 3872779387800806189906621)
            ·
              refine ⟨1452292270425302321214983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3872779387800806189906621 1452292270425302321214983)
              ·
                refine ⟨2178438405637953481822475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452292270425302321214983 2178438405637953481822475)
                ·
                  refine ⟨3267657608456930222733713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178438405637953481822475 3267657608456930222733713)
                  ·
                    refine ⟨2450743206342697667050285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267657608456930222733713 2450743206342697667050285)
                    ·
                      refine ⟨919028702378511625143857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450743206342697667050285 919028702378511625143857)
                      ·
                        rfl

theorem cell23_1789802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1789802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789802 prefixEnd_1789802 := by exact prefixLift 1789802
  have htrace : WordTrace (prefixWord ++ tailWord_1789802) baseStart_1789802 baseEnd_1789802 := by
    simpa [prefixWord, tailWord_1789802, baseEnd_1789802] using wordTrace_append hprefix tailTrace_1789802
  have hstable : (prefixWord ++ tailWord_1789802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789802).length < 2 ^ (prefixWord ++ tailWord_1789802).sum := by decide
  have hdescent : baseEnd_1789802 < baseStart_1789802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789821 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_1789821 : Nat := 118140960795 + 1789821 * 2 ^ 59
def prefixEnd_1789821 : Nat := 4983230072969 + 3 ^ 40 * 1789821 * 2
def baseEnd_1789821 : Nat := 919038458510947050806269

theorem tailTrace_1789821 : CollatzResearch.WordTrace tailWord_1789821 prefixEnd_1789821 919038458510947050806269 := by
  unfold tailWord_1789821
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280134848791668935713317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43520089899194445957142211 65280134848791668935713317)
  ·
    refine ⟨12240025284148437925446247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65280134848791668935713317 12240025284148437925446247)
    ·
      refine ⟨18360037926222656888169371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240025284148437925446247 18360037926222656888169371)
      ·
        refine ⟨27540056889333985332254057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18360037926222656888169371 27540056889333985332254057)
        ·
          refine ⟨20655042667000488999190543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27540056889333985332254057 20655042667000488999190543)
          ·
            refine ⟨30982564000500733498785815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655042667000488999190543 30982564000500733498785815)
            ·
              refine ⟨46473846000751100248178723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30982564000500733498785815 46473846000751100248178723)
              ·
                refine ⟨69710769001126650372268085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46473846000751100248178723 69710769001126650372268085)
                ·
                  refine ⟨6535384593855623472400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69710769001126650372268085 6535384593855623472400133)
                  ·
                    refine ⟨1225384611347929401075025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535384593855623472400133 1225384611347929401075025)
                    ·
                      refine ⟨919038458510947050806269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225384611347929401075025 919038458510947050806269)
                      ·
                        rfl

theorem cell23_1789821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_1789821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789821 prefixEnd_1789821 := by exact prefixLift 1789821
  have htrace : WordTrace (prefixWord ++ tailWord_1789821) baseStart_1789821 baseEnd_1789821 := by
    simpa [prefixWord, tailWord_1789821, baseEnd_1789821] using wordTrace_append hprefix tailTrace_1789821
  have hstable : (prefixWord ++ tailWord_1789821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789821).length < 2 ^ (prefixWord ++ tailWord_1789821).sum := by decide
  have hdescent : baseEnd_1789821 < baseStart_1789821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789824 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1789824 : Nat := 118140960795 + 1789824 * 2 ^ 59
def prefixEnd_1789824 : Nat := 4983230072969 + 3 ^ 40 * 1789824 * 2
def baseEnd_1789824 : Nat := 919039998952910539068755

theorem tailTrace_1789824 : CollatzResearch.WordTrace tailWord_1789824 prefixEnd_1789824 919039998952910539068755 := by
  unfold tailWord_1789824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32640122133890400224036263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43520162845187200298715017 32640122133890400224036263)
  ·
    refine ⟨48960183200835600336054395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32640122133890400224036263 48960183200835600336054395)
    ·
      refine ⟨73440274801253400504081593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48960183200835600336054395 73440274801253400504081593)
      ·
        refine ⟨55080206100940050378061195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73440274801253400504081593 55080206100940050378061195)
        ·
          refine ⟨82620309151410075567091793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55080206100940050378061195 82620309151410075567091793)
          ·
            refine ⟨61965231863557556675318845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82620309151410075567091793 61965231863557556675318845)
            ·
              refine ⟨23236961948834083753244567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61965231863557556675318845 23236961948834083753244567)
              ·
                refine ⟨34855442923251125629866851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23236961948834083753244567 34855442923251125629866851)
                ·
                  refine ⟨52283164384876688444800277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34855442923251125629866851 52283164384876688444800277)
                  ·
                    refine ⟨2450773330541094770850013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52283164384876688444800277 2450773330541094770850013)
                    ·
                      refine ⟨919039998952910539068755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2450773330541094770850013 919039998952910539068755)
                      ·
                        rfl

theorem cell23_1789824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1789824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789824 prefixEnd_1789824 := by exact prefixLift 1789824
  have htrace : WordTrace (prefixWord ++ tailWord_1789824) baseStart_1789824 baseEnd_1789824 := by
    simpa [prefixWord, tailWord_1789824, baseEnd_1789824] using wordTrace_append hprefix tailTrace_1789824
  have hstable : (prefixWord ++ tailWord_1789824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789824).length < 2 ^ (prefixWord ++ tailWord_1789824).sum := by decide
  have hdescent : baseEnd_1789824 < baseStart_1789824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789831 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1789831 : Nat := 118140960795 + 1789831 * 2 ^ 59
def prefixEnd_1789831 : Nat := 4983230072969 + 3 ^ 40 * 1789831 * 2
def baseEnd_1789831 : Nat := 306347864439164003893741

theorem tailTrace_1789831 : CollatzResearch.WordTrace tailWord_1789831 prefixEnd_1789831 306347864439164003893741 := by
  unfold tailWord_1789831
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280499578755440643577347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43520333052503627095718231 65280499578755440643577347)
  ·
    refine ⟨97920749368133160965366021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65280499578755440643577347 97920749368133160965366021)
    ·
      refine ⟨18360140506524967681006129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97920749368133160965366021 18360140506524967681006129)
      ·
        refine ⟨13770105379893725760754597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18360140506524967681006129 13770105379893725760754597)
        ·
          refine ⟨2581894758730073580141487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13770105379893725760754597 2581894758730073580141487)
          ·
            refine ⟨3872842138095110370212231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581894758730073580141487 3872842138095110370212231)
            ·
              refine ⟨5809263207142665555318347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872842138095110370212231 5809263207142665555318347)
              ·
                refine ⟨8713894810713998332977521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809263207142665555318347 8713894810713998332977521)
                ·
                  refine ⟨6535421108035498749733141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713894810713998332977521 6535421108035498749733141)
                  ·
                    refine ⟨306347864439164003893741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6535421108035498749733141 306347864439164003893741)
                    ·
                      rfl

theorem cell23_1789831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1789831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789831 prefixEnd_1789831 := by exact prefixLift 1789831
  have htrace : WordTrace (prefixWord ++ tailWord_1789831) baseStart_1789831 baseEnd_1789831 := by
    simpa [prefixWord, tailWord_1789831, baseEnd_1789831] using wordTrace_append hprefix tailTrace_1789831
  have hstable : (prefixWord ++ tailWord_1789831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789831).length < 2 ^ (prefixWord ++ tailWord_1789831).sum := by decide
  have hdescent : baseEnd_1789831 < baseStart_1789831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789911 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1789911 : Nat := 118140960795 + 1789911 * 2 ^ 59
def prefixEnd_1789911 : Nat := 4983230072969 + 3 ^ 40 * 1789911 * 2
def baseEnd_1789911 : Nat := 919084671769851698680855

theorem tailTrace_1789911 : CollatzResearch.WordTrace tailWord_1789911 prefixEnd_1789911 919084671769851698680855 := by
  unfold tailWord_1789911
  simp only [CollatzResearch.WordTrace]
  refine ⟨65283417418465614306489587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43522278278977076204326391 65283417418465614306489587)
  ·
    refine ⟨97925126127698421459734381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65283417418465614306489587 97925126127698421459734381)
    ·
      refine ⟨36721922297886908047400393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97925126127698421459734381 36721922297886908047400393)
      ·
        refine ⟨27541441723415181035550295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36721922297886908047400393 27541441723415181035550295)
        ·
          refine ⟨41312162585122771553325443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27541441723415181035550295 41312162585122771553325443)
          ·
            refine ⟨61968243877684157329988165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41312162585122771553325443 61968243877684157329988165)
            ·
              refine ⟨11619045727065779499372781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61968243877684157329988165 11619045727065779499372781)
              ·
                refine ⟨4357142147649667312264793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11619045727065779499372781 4357142147649667312264793)
                ·
                  refine ⟨3267856610737250484198595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357142147649667312264793 3267856610737250484198595)
                  ·
                    refine ⟨4901784916105875726297893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267856610737250484198595 4901784916105875726297893)
                    ·
                      refine ⟨919084671769851698680855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4901784916105875726297893 919084671769851698680855)
                      ·
                        rfl

theorem cell23_1789911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1789911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789911 prefixEnd_1789911 := by exact prefixLift 1789911
  have htrace : WordTrace (prefixWord ++ tailWord_1789911) baseStart_1789911 baseEnd_1789911 := by
    simpa [prefixWord, tailWord_1789911, baseEnd_1789911] using wordTrace_append hprefix tailTrace_1789911
  have hstable : (prefixWord ++ tailWord_1789911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789911).length < 2 ^ (prefixWord ++ tailWord_1789911).sum := by decide
  have hdescent : baseEnd_1789911 < baseStart_1789911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789921 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1789921 : Nat := 118140960795 + 1789921 * 2 ^ 59
def prefixEnd_1789921 : Nat := 4983230072969 + 3 ^ 40 * 1789921 * 2
def baseEnd_1789921 : Nat := 306363268858798886518603

theorem tailTrace_1789921 : CollatzResearch.WordTrace tailWord_1789921 prefixEnd_1789921 306363268858798886518603 := by
  unfold tailWord_1789921
  simp only [CollatzResearch.WordTrace]
  refine ⟨65283782148429386014353617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43522521432286257342902411 65283782148429386014353617)
  ·
    refine ⟨48962836611322039510765213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65283782148429386014353617 48962836611322039510765213)
    ·
      refine ⟨18361063729245764816536955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48962836611322039510765213 18361063729245764816536955)
      ·
        refine ⟨27541595593868647224805433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361063729245764816536955 27541595593868647224805433)
        ·
          refine ⟨20656196695401485418604075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27541595593868647224805433 20656196695401485418604075)
          ·
            refine ⟨30984295043102228127906113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20656196695401485418604075 30984295043102228127906113)
            ·
              refine ⟨23238221282326671095929585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30984295043102228127906113 23238221282326671095929585)
              ·
                refine ⟨17428665961745003321947189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23238221282326671095929585 17428665961745003321947189)
                ·
                  refine ⟨1633937433913594061432549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17428665961745003321947189 1633937433913594061432549)
                  ·
                    refine ⟨306363268858798886518603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633937433913594061432549 306363268858798886518603)
                    ·
                      rfl

theorem cell23_1789921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1789921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789921 prefixEnd_1789921 := by exact prefixLift 1789921
  have htrace : WordTrace (prefixWord ++ tailWord_1789921) baseStart_1789921 baseEnd_1789921 := by
    simpa [prefixWord, tailWord_1789921, baseEnd_1789921] using wordTrace_append hprefix tailTrace_1789921
  have hstable : (prefixWord ++ tailWord_1789921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789921).length < 2 ^ (prefixWord ++ tailWord_1789921).sum := by decide
  have hdescent : baseEnd_1789921 < baseStart_1789921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789998 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1789998 : Nat := 118140960795 + 1789998 * 2 ^ 59
def prefixEnd_1789998 : Nat := 4983230072969 + 3 ^ 40 * 1789998 * 2
def baseEnd_1789998 : Nat := 306376448195597619430985

theorem tailTrace_1789998 : CollatzResearch.WordTrace tailWord_1789998 prefixEnd_1789998 306376448195597619430985 := by
  unfold tailWord_1789998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160823821143803520613331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43524393712766952109937765 8160823821143803520613331)
  ·
    refine ⟨12241235731715705280919997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8160823821143803520613331 12241235731715705280919997)
    ·
      refine ⟨4590463399393389480344999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12241235731715705280919997 4590463399393389480344999)
      ·
        refine ⟨6885695099090084220517499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590463399393389480344999 6885695099090084220517499)
        ·
          refine ⟨10328542648635126330776249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885695099090084220517499 10328542648635126330776249)
          ·
            refine ⟨7746406986476344748082187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10328542648635126330776249 7746406986476344748082187)
            ·
              refine ⟨11619610479714517122123281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746406986476344748082187 11619610479714517122123281)
              ·
                refine ⟨8714707859785887841592461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11619610479714517122123281 8714707859785887841592461)
                ·
                  refine ⟨3268015447419707940597173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8714707859785887841592461 3268015447419707940597173)
                  ·
                    refine ⟨306376448195597619430985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3268015447419707940597173 306376448195597619430985)
                    ·
                      rfl

theorem cell23_1789998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1789998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1789998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1789998 prefixEnd_1789998 := by exact prefixLift 1789998
  have htrace : WordTrace (prefixWord ++ tailWord_1789998) baseStart_1789998 baseEnd_1789998 := by
    simpa [prefixWord, tailWord_1789998, baseEnd_1789998] using wordTrace_append hprefix tailTrace_1789998
  have hstable : (prefixWord ++ tailWord_1789998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789998).length < 2 ^ (prefixWord ++ tailWord_1789998).sum := by decide
  have hdescent : baseEnd_1789998 < baseStart_1789998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790022 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1790022 : Nat := 118140960795 + 1790022 * 2 ^ 59
def prefixEnd_1790022 : Nat := 4983230072969 + 3 ^ 40 * 1790022 * 2
def baseEnd_1790022 : Nat := 919141668122500764392845

theorem tailTrace_1790022 : CollatzResearch.WordTrace tailWord_1790022 prefixEnd_1790022 919141668122500764392845 := by
  unfold tailWord_1790022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040233310033233758243135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43524977280708986842520213 2040233310033233758243135)
  ·
    refine ⟨3060349965049850637364703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2040233310033233758243135 3060349965049850637364703)
    ·
      refine ⟨4590524947574775956047055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060349965049850637364703 4590524947574775956047055)
      ·
        refine ⟨6885787421362163934070583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590524947574775956047055 6885787421362163934070583)
        ·
          refine ⟨10328681132043245901105875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885787421362163934070583 10328681132043245901105875)
          ·
            refine ⟨15493021698064868851658813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328681132043245901105875 15493021698064868851658813)
            ·
              refine ⟨5809883136774325819372055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15493021698064868851658813 5809883136774325819372055)
              ·
                refine ⟨8714824705161488729058083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809883136774325819372055 8714824705161488729058083)
                ·
                  refine ⟨13072237057742233093587125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714824705161488729058083 13072237057742233093587125)
                  ·
                    refine ⟨1225522224163334352523793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13072237057742233093587125 1225522224163334352523793)
                    ·
                      refine ⟨919141668122500764392845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225522224163334352523793 919141668122500764392845)
                      ·
                        rfl

theorem cell23_1790022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1790022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790022 prefixEnd_1790022 := by exact prefixLift 1790022
  have htrace : WordTrace (prefixWord ++ tailWord_1790022) baseStart_1790022 baseEnd_1790022 := by
    simpa [prefixWord, tailWord_1790022, baseEnd_1790022] using wordTrace_append hprefix tailTrace_1790022
  have hstable : (prefixWord ++ tailWord_1790022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790022).length < 2 ^ (prefixWord ++ tailWord_1790022).sum := by decide
  have hdescent : baseEnd_1790022 < baseStart_1790022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790029 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_1790029 : Nat := 118140960795 + 1790029 * 2 ^ 59
def prefixEnd_1790029 : Nat := 4983230072969 + 3 ^ 40 * 1790029 * 2
def baseEnd_1790029 : Nat := 919145262487082237005313

theorem tailTrace_1790029 : CollatzResearch.WordTrace tailWord_1790029 prefixEnd_1790029 919145262487082237005313 := by
  unfold tailWord_1790029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65287721232038120459285141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43525147488025413639523427 65287721232038120459285141)
  ·
    refine ⟨3060361932751786896528991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65287721232038120459285141 3060361932751786896528991)
    ·
      refine ⟨4590542899127680344793487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060361932751786896528991 4590542899127680344793487)
      ·
        refine ⟨6885814348691520517190231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590542899127680344793487 6885814348691520517190231)
        ·
          refine ⟨10328721523037280775785347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885814348691520517190231 10328721523037280775785347)
          ·
            refine ⟨15493082284555921163678021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328721523037280775785347 15493082284555921163678021)
            ·
              refine ⟨2904952928354235218189629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15493082284555921163678021 2904952928354235218189629)
              ·
                refine ⟨1089357348132838206821111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904952928354235218189629 1089357348132838206821111)
                ·
                  refine ⟨1634036022199257310231667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089357348132838206821111 1634036022199257310231667)
                  ·
                    refine ⟨2451054033298885965347501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634036022199257310231667 2451054033298885965347501)
                    ·
                      refine ⟨919145262487082237005313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451054033298885965347501 919145262487082237005313)
                      ·
                        rfl

theorem cell23_1790029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_1790029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790029 prefixEnd_1790029 := by exact prefixLift 1790029
  have htrace : WordTrace (prefixWord ++ tailWord_1790029) baseStart_1790029 baseEnd_1790029 := by
    simpa [prefixWord, tailWord_1790029, baseEnd_1790029] using wordTrace_append hprefix tailTrace_1790029
  have hstable : (prefixWord ++ tailWord_1790029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790029).length < 2 ^ (prefixWord ++ tailWord_1790029).sum := by decide
  have hdescent : baseEnd_1790029 < baseStart_1790029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790046 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1790046 : Nat := 118140960795 + 1790046 * 2 ^ 59
def prefixEnd_1790046 : Nat := 4983230072969 + 3 ^ 40 * 1790046 * 2
def baseEnd_1790046 : Nat := 919153991658208670492735

theorem tailTrace_1790046 : CollatzResearch.WordTrace tailWord_1790046 prefixEnd_1790046 919153991658208670492735 := by
  unfold tailWord_1790046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161042659122066545331749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43525560848651021575102661 8161042659122066545331749)
  ·
    refine ⟨1530195498585387477249703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8161042659122066545331749 1530195498585387477249703)
    ·
      refine ⟨2295293247878081215874555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530195498585387477249703 2295293247878081215874555)
      ·
        refine ⟨3442939871817121823811833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295293247878081215874555 3442939871817121823811833)
        ·
          refine ⟨2582204903862841367858875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442939871817121823811833 2582204903862841367858875)
          ·
            refine ⟨3873307355794262051788313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582204903862841367858875 3873307355794262051788313)
            ·
              refine ⟨2904980516845696538841235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873307355794262051788313 2904980516845696538841235)
              ·
                refine ⟨4357470775268544808261853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904980516845696538841235 4357470775268544808261853)
                ·
                  refine ⟨1634051540725704303098195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4357470775268544808261853 1634051540725704303098195)
                  ·
                    refine ⟨2451077311088556454647293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634051540725704303098195 2451077311088556454647293)
                    ·
                      refine ⟨919153991658208670492735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451077311088556454647293 919153991658208670492735)
                      ·
                        rfl

theorem cell23_1790046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1790046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790046 prefixEnd_1790046 := by exact prefixLift 1790046
  have htrace : WordTrace (prefixWord ++ tailWord_1790046) baseStart_1790046 baseEnd_1790046 := by
    simpa [prefixWord, tailWord_1790046, baseEnd_1790046] using wordTrace_append hprefix tailTrace_1790046
  have hstable : (prefixWord ++ tailWord_1790046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790046).length < 2 ^ (prefixWord ++ tailWord_1790046).sum := by decide
  have hdescent : baseEnd_1790046 < baseStart_1790046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790062 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1790062 : Nat := 118140960795 + 1790062 * 2 ^ 59
def prefixEnd_1790062 : Nat := 4983230072969 + 3 ^ 40 * 1790062 * 2
def baseEnd_1790062 : Nat := 306387402449560202630887

theorem tailTrace_1790062 : CollatzResearch.WordTrace tailWord_1790062 prefixEnd_1790062 306387402449560202630887 := by
  unfold tailWord_1790062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161115605114820886904555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43525949893945711396824293 8161115605114820886904555)
  ·
    refine ⟨12241673407672231330356833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161115605114820886904555 12241673407672231330356833)
    ·
      refine ⟨9181255055754173497767625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12241673407672231330356833 9181255055754173497767625)
      ·
        refine ⟨6885941291815630123325719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9181255055754173497767625 6885941291815630123325719)
        ·
          refine ⟨10328911937723445184988579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885941291815630123325719 10328911937723445184988579)
          ·
            refine ⟨15493367906585167777482869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328911937723445184988579 15493367906585167777482869)
            ·
              refine ⟨1452503241242359479139019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15493367906585167777482869 1452503241242359479139019)
              ·
                refine ⟨2178754861863539218708529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452503241242359479139019 2178754861863539218708529)
                ·
                  refine ⟨1634066146397654414031397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2178754861863539218708529 1634066146397654414031397)
                  ·
                    refine ⟨306387402449560202630887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634066146397654414031397 306387402449560202630887)
                    ·
                      rfl

theorem cell23_1790062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1790062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790062 prefixEnd_1790062 := by exact prefixLift 1790062
  have htrace : WordTrace (prefixWord ++ tailWord_1790062) baseStart_1790062 baseEnd_1790062 := by
    simpa [prefixWord, tailWord_1790062, baseEnd_1790062] using wordTrace_append hprefix tailTrace_1790062
  have hstable : (prefixWord ++ tailWord_1790062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790062).length < 2 ^ (prefixWord ++ tailWord_1790062).sum := by decide
  have hdescent : baseEnd_1790062 < baseStart_1790062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790085 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_1790085 : Nat := 118140960795 + 1790085 * 2 ^ 59
def prefixEnd_1790085 : Nat := 4983230072969 + 3 ^ 40 * 1790085 * 2
def baseEnd_1790085 : Nat := 919174017403734017905055

theorem tailTrace_1790085 : CollatzResearch.WordTrace tailWord_1790085 prefixEnd_1790085 919174017403734017905055 := by
  unfold tailWord_1790085
  simp only [CollatzResearch.WordTrace]
  refine ⟨65289763719835242023323709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43526509146556828015549139 65289763719835242023323709)
  ·
    refine ⟨24483661394938215758746391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65289763719835242023323709 24483661394938215758746391)
    ·
      refine ⟨36725492092407323638119587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483661394938215758746391 36725492092407323638119587)
      ·
        refine ⟨55088238138610985457179381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36725492092407323638119587 55088238138610985457179381)
        ·
          refine ⟨5164522325494779886610567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55088238138610985457179381 5164522325494779886610567)
          ·
            refine ⟨7746783488242169829915851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164522325494779886610567 7746783488242169829915851)
            ·
              refine ⟨11620175232363254744873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746783488242169829915851 11620175232363254744873777)
              ·
                refine ⟨8715131424272441058655333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11620175232363254744873777 8715131424272441058655333)
                ·
                  refine ⟨1634087142051082698497875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8715131424272441058655333 1634087142051082698497875)
                  ·
                    refine ⟨2451130713076624047746813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634087142051082698497875 2451130713076624047746813)
                    ·
                      refine ⟨919174017403734017905055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451130713076624047746813 919174017403734017905055)
                      ·
                        rfl

theorem cell23_1790085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_1790085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790085 prefixEnd_1790085 := by exact prefixLift 1790085
  have htrace : WordTrace (prefixWord ++ tailWord_1790085) baseStart_1790085 baseEnd_1790085 := by
    simpa [prefixWord, tailWord_1790085, baseEnd_1790085] using wordTrace_append hprefix tailTrace_1790085
  have hstable : (prefixWord ++ tailWord_1790085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790085).length < 2 ^ (prefixWord ++ tailWord_1790085).sum := by decide
  have hdescent : baseEnd_1790085 < baseStart_1790085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790091 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_1790091 : Nat := 118140960795 + 1790091 * 2 ^ 59
def prefixEnd_1790091 : Nat := 4983230072969 + 3 ^ 40 * 1790091 * 2
def baseEnd_1790091 : Nat := 919177098287660994430027

theorem tailTrace_1790091 : CollatzResearch.WordTrace tailWord_1790091 prefixEnd_1790091 919177098287660994430027 := by
  unfold tailWord_1790091
  simp only [CollatzResearch.WordTrace]
  refine ⟨65289982557813505048042127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43526655038542336698694751 65289982557813505048042127)
  ·
    refine ⟨97934973836720257572063191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65289982557813505048042127 97934973836720257572063191)
    ·
      refine ⟨146902460755080386358094787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97934973836720257572063191 146902460755080386358094787)
      ·
        refine ⟨220353691132620579537142181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146902460755080386358094787 220353691132620579537142181)
        ·
          refine ⟨41316317087366358663214159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220353691132620579537142181 41316317087366358663214159)
          ·
            refine ⟨61974475631049537994821239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41316317087366358663214159 61974475631049537994821239)
            ·
              refine ⟨92961713446574306992231859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61974475631049537994821239 92961713446574306992231859)
              ·
                refine ⟨139442570169861460488347789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92961713446574306992231859 139442570169861460488347789)
                ·
                  refine ⟨52290963813698047683130421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139442570169861460488347789 52290963813698047683130421)
                  ·
                    refine ⟨4902277857534191970293477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52290963813698047683130421 4902277857534191970293477)
                    ·
                      refine ⟨919177098287660994430027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4902277857534191970293477 919177098287660994430027)
                      ·
                        rfl

theorem cell23_1790091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_1790091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790091 prefixEnd_1790091 := by exact prefixLift 1790091
  have htrace : WordTrace (prefixWord ++ tailWord_1790091) baseStart_1790091 baseEnd_1790091 := by
    simpa [prefixWord, tailWord_1790091, baseEnd_1790091] using wordTrace_append hprefix tailTrace_1790091
  have hstable : (prefixWord ++ tailWord_1790091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790091).length < 2 ^ (prefixWord ++ tailWord_1790091).sum := by decide
  have hdescent : baseEnd_1790091 < baseStart_1790091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790098 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1790098 : Nat := 118140960795 + 1790098 * 2 ^ 59
def prefixEnd_1790098 : Nat := 4983230072969 + 3 ^ 40 * 1790098 * 2
def baseEnd_1790098 : Nat := 919180692652242467042495

theorem tailTrace_1790098 : CollatzResearch.WordTrace tailWord_1790098 prefixEnd_1790098 919180692652242467042495 := by
  unfold tailWord_1790098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322559467197036310886737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43526825245858763495697965 16322559467197036310886737)
  ·
    refine ⟨12241919600397777233165053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16322559467197036310886737 12241919600397777233165053)
    ·
      refine ⟨4590719850149166462436895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12241919600397777233165053 4590719850149166462436895)
      ·
        refine ⟨6886079775223749693655343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590719850149166462436895 6886079775223749693655343)
        ·
          refine ⟨10329119662835624540483015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886079775223749693655343 10329119662835624540483015)
          ·
            refine ⟨15493679494253436810724523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329119662835624540483015 15493679494253436810724523)
            ·
              refine ⟨23240519241380155216086785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15493679494253436810724523 23240519241380155216086785)
              ·
                refine ⟨17430389431035116412065089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23240519241380155216086785 17430389431035116412065089)
                ·
                  refine ⟨13072792073276337309048817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17430389431035116412065089 13072792073276337309048817)
                  ·
                    refine ⟨9804594054957252981786613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13072792073276337309048817 9804594054957252981786613)
                    ·
                      refine ⟨919180692652242467042495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9804594054957252981786613 919180692652242467042495)
                      ·
                        rfl

theorem cell23_1790098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1790098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790098 prefixEnd_1790098 := by exact prefixLift 1790098
  have htrace : WordTrace (prefixWord ++ tailWord_1790098) baseStart_1790098 baseEnd_1790098 := by
    simpa [prefixWord, tailWord_1790098, baseEnd_1790098] using wordTrace_append hprefix tailTrace_1790098
  have hstable : (prefixWord ++ tailWord_1790098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790098).length < 2 ^ (prefixWord ++ tailWord_1790098).sum := by decide
  have hdescent : baseEnd_1790098 < baseStart_1790098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790108 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1790108 : Nat := 118140960795 + 1790108 * 2 ^ 59
def prefixEnd_1790108 : Nat := 4983230072969 + 3 ^ 40 * 1790108 * 2
def baseEnd_1790108 : Nat := 919185827458787427917449

theorem tailTrace_1790108 : CollatzResearch.WordTrace tailWord_1790108 prefixEnd_1790108 919185827458787427917449 := by
  unfold tailWord_1790108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32645301299375958475705489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43527068399167944634273985 32645301299375958475705489)
  ·
    refine ⟨24483975974531968856779117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32645301299375958475705489 24483975974531968856779117)
    ·
      refine ⟨9181490990449488321292169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24483975974531968856779117 9181490990449488321292169)
      ·
        refine ⟨6886118242837116240969127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9181490990449488321292169 6886118242837116240969127)
        ·
          refine ⟨10329177364255674361453691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886118242837116240969127 10329177364255674361453691)
          ·
            refine ⟨15493766046383511542180537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329177364255674361453691 15493766046383511542180537)
            ·
              refine ⟨11620324534787633656635403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15493766046383511542180537 11620324534787633656635403)
              ·
                refine ⟨17430486802181450484953105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11620324534787633656635403 17430486802181450484953105)
                ·
                  refine ⟨13072865101636087863714829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17430486802181450484953105 13072865101636087863714829)
                  ·
                    refine ⟨4902324413113532948893061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13072865101636087863714829 4902324413113532948893061)
                    ·
                      refine ⟨919185827458787427917449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4902324413113532948893061 919185827458787427917449)
                      ·
                        rfl

theorem cell23_1790108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1790108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790108 prefixEnd_1790108 := by exact prefixLift 1790108
  have htrace : WordTrace (prefixWord ++ tailWord_1790108) baseStart_1790108 baseEnd_1790108 := by
    simpa [prefixWord, tailWord_1790108, baseEnd_1790108] using wordTrace_append hprefix tailTrace_1790108
  have hstable : (prefixWord ++ tailWord_1790108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790108).length < 2 ^ (prefixWord ++ tailWord_1790108).sum := by decide
  have hdescent : baseEnd_1790108 < baseStart_1790108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790119 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1790119 : Nat := 118140960795 + 1790119 * 2 ^ 59
def prefixEnd_1790119 : Nat := 4983230072969 + 3 ^ 40 * 1790119 * 2
def baseEnd_1790119 : Nat := 919191475745986884879899

theorem tailTrace_1790119 : CollatzResearch.WordTrace tailWord_1790119 prefixEnd_1790119 919191475745986884879899 := by
  unfold tailWord_1790119
  simp only [CollatzResearch.WordTrace]
  refine ⟨65291003801712065830061411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43527335867808043886707607 65291003801712065830061411)
  ·
    refine ⟨97936505702568098745092117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65291003801712065830061411 97936505702568098745092117)
    ·
      refine ⟨4590773704807879628676193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97936505702568098745092117 4590773704807879628676193)
      ·
        refine ⟨3443080278605909721507145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590773704807879628676193 3443080278605909721507145)
        ·
          refine ⟨2582310208954432291130359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443080278605909721507145 2582310208954432291130359)
          ·
            refine ⟨3873465313431648436695539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582310208954432291130359 3873465313431648436695539)
            ·
              refine ⟨5810197970147472655043309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873465313431648436695539 5810197970147472655043309)
              ·
                refine ⟨2178824238805302245641241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810197970147472655043309 2178824238805302245641241)
                ·
                  refine ⟨1634118179103976684230931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2178824238805302245641241 1634118179103976684230931)
                  ·
                    refine ⟨2451177268655965026346397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634118179103976684230931 2451177268655965026346397)
                    ·
                      refine ⟨919191475745986884879899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451177268655965026346397 919191475745986884879899)
                      ·
                        rfl

theorem cell23_1790119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1790119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790119 prefixEnd_1790119 := by exact prefixLift 1790119
  have htrace : WordTrace (prefixWord ++ tailWord_1790119) baseStart_1790119 baseEnd_1790119 := by
    simpa [prefixWord, tailWord_1790119, baseEnd_1790119] using wordTrace_append hprefix tailTrace_1790119
  have hstable : (prefixWord ++ tailWord_1790119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790119).length < 2 ^ (prefixWord ++ tailWord_1790119).sum := by decide
  have hdescent : baseEnd_1790119 < baseStart_1790119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790131 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 9]
def baseStart_1790131 : Nat := 118140960795 + 1790131 * 2 ^ 59
def prefixEnd_1790131 : Nat := 4983230072969 + 3 ^ 40 * 1790131 * 2
def baseEnd_1790131 : Nat := 102133070834871204214427

theorem tailTrace_1790131 : CollatzResearch.WordTrace tailWord_1790131 prefixEnd_1790131 102133070834871204214427 := by
  unfold tailWord_1790131
  simp only [CollatzResearch.WordTrace]
  refine ⟨65291441477668591879498247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43527627651779061252998831 65291441477668591879498247)
  ·
    refine ⟨97937162216502887819247371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65291441477668591879498247 97937162216502887819247371)
    ·
      refine ⟨146905743324754331728871057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97937162216502887819247371 146905743324754331728871057)
      ·
        refine ⟨110179307493565748796653293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146905743324754331728871057 110179307493565748796653293)
        ·
          refine ⟨41317240310087155798744985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110179307493565748796653293 41317240310087155798744985)
          ·
            refine ⟨30987930232565366849058739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41317240310087155798744985 30987930232565366849058739)
            ·
              refine ⟨46481895348848050273588109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30987930232565366849058739 46481895348848050273588109)
              ·
                refine ⟨17430710755818018852595541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46481895348848050273588109 17430710755818018852595541)
                ·
                  refine ⟨102133070834871204214427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17430710755818018852595541 102133070834871204214427)
                  ·
                    rfl

theorem cell23_1790131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 9].length) (baseStart_1790131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790131 prefixEnd_1790131 := by exact prefixLift 1790131
  have htrace : WordTrace (prefixWord ++ tailWord_1790131) baseStart_1790131 baseEnd_1790131 := by
    simpa [prefixWord, tailWord_1790131, baseEnd_1790131] using wordTrace_append hprefix tailTrace_1790131
  have hstable : (prefixWord ++ tailWord_1790131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790131).length < 2 ^ (prefixWord ++ tailWord_1790131).sum := by decide
  have hdescent : baseEnd_1790131 < baseStart_1790131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790218 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1790218 : Nat := 118140960795 + 1790218 * 2 ^ 59
def prefixEnd_1790218 : Nat := 4983230072969 + 3 ^ 40 * 1790218 * 2
def baseEnd_1790218 : Nat := 919242310330781997541943

theorem tailTrace_1790218 : CollatzResearch.WordTrace tailWord_1790218 prefixEnd_1790218 919242310330781997541943 := by
  unfold tailWord_1790218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323653657088351434478827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43529743085568937158610205 16323653657088351434478827)
  ·
    refine ⟨24485480485632527151718241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16323653657088351434478827 24485480485632527151718241)
    ·
      refine ⟨18364110364224395363788681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24485480485632527151718241 18364110364224395363788681)
      ·
        refine ⟨13773082773168296522841511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18364110364224395363788681 13773082773168296522841511)
        ·
          refine ⟨20659624159752444784262267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773082773168296522841511 20659624159752444784262267)
          ·
            refine ⟨30989436239628667176393401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659624159752444784262267 30989436239628667176393401)
            ·
              refine ⟨23242077179721500382295051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30989436239628667176393401 23242077179721500382295051)
              ·
                refine ⟨34863115769582250573442577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23242077179721500382295051 34863115769582250573442577)
                ·
                  refine ⟨26147336827186687930081933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34863115769582250573442577 26147336827186687930081933)
                  ·
                    refine ⟨9805251310195007973780725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26147336827186687930081933 9805251310195007973780725)
                    ·
                      refine ⟨919242310330781997541943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9805251310195007973780725 919242310330781997541943)
                      ·
                        rfl

theorem cell23_1790218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1790218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790218 prefixEnd_1790218 := by exact prefixLift 1790218
  have htrace : WordTrace (prefixWord ++ tailWord_1790218) baseStart_1790218 baseEnd_1790218 := by
    simpa [prefixWord, tailWord_1790218, baseEnd_1790218] using wordTrace_append hprefix tailTrace_1790218
  have hstable : (prefixWord ++ tailWord_1790218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790218).length < 2 ^ (prefixWord ++ tailWord_1790218).sum := by decide
  have hdescent : baseEnd_1790218 < baseStart_1790218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790225 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_1790225 : Nat := 118140960795 + 1790225 * 2 ^ 59
def prefixEnd_1790225 : Nat := 4983230072969 + 3 ^ 40 * 1790225 * 2
def baseEnd_1790225 : Nat := 306415301565121156718137

theorem tailTrace_1790225 : CollatzResearch.WordTrace tailWord_1790225 prefixEnd_1790225 306415301565121156718137 := by
  unfold tailWord_1790225
  simp only [CollatzResearch.WordTrace]
  refine ⟨65294869939328045933420129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43529913292885363955613419 65294869939328045933420129)
  ·
    refine ⟨48971152454496034450065097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65294869939328045933420129 48971152454496034450065097)
    ·
      refine ⟨36728364340872025837548823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48971152454496034450065097 36728364340872025837548823)
      ·
        refine ⟨55092546511308038756323235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36728364340872025837548823 55092546511308038756323235)
        ·
          refine ⟨82638819766962058134484853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55092546511308038756323235 82638819766962058134484853)
          ·
            refine ⟨7747389353152692950107955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82638819766962058134484853 7747389353152692950107955)
            ·
              refine ⟨11621084029729039425161933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747389353152692950107955 11621084029729039425161933)
              ·
                refine ⟨4357906511148389784435725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11621084029729039425161933 4357906511148389784435725)
                ·
                  refine ⟨1634214941680646169163397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4357906511148389784435725 1634214941680646169163397)
                  ·
                    refine ⟨306415301565121156718137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634214941680646169163397 306415301565121156718137)
                    ·
                      rfl

theorem cell23_1790225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_1790225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790225 prefixEnd_1790225 := by exact prefixLift 1790225
  have htrace : WordTrace (prefixWord ++ tailWord_1790225) baseStart_1790225 baseEnd_1790225 := by
    simpa [prefixWord, tailWord_1790225, baseEnd_1790225] using wordTrace_append hprefix tailTrace_1790225
  have hstable : (prefixWord ++ tailWord_1790225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790225).length < 2 ^ (prefixWord ++ tailWord_1790225).sum := by decide
  have hdescent : baseEnd_1790225 < baseStart_1790225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790242 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1790242 : Nat := 118140960795 + 1790242 * 2 ^ 59
def prefixEnd_1790242 : Nat := 4983230072969 + 3 ^ 40 * 1790242 * 2
def baseEnd_1790242 : Nat := 306418211288829967880611

theorem tailTrace_1790242 : CollatzResearch.WordTrace tailWord_1790242 prefixEnd_1790242 306418211288829967880611 := by
  unfold tailWord_1790242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323872495066614459197245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43530326653510971891192653 16323872495066614459197245)
  ·
    refine ⟨6121452185649980422198967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16323872495066614459197245 6121452185649980422198967)
    ·
      refine ⟨9182178278474970633298451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121452185649980422198967 9182178278474970633298451)
      ·
        refine ⟨13773267417712455949947677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182178278474970633298451 13773267417712455949947677)
        ·
          refine ⟨5164975281642170981230379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13773267417712455949947677 5164975281642170981230379)
          ·
            refine ⟨7747462922463256471845569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164975281642170981230379 7747462922463256471845569)
            ·
              refine ⟨5810597191847442353884177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747462922463256471845569 5810597191847442353884177)
              ·
                refine ⟨4357947893885581765413133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810597191847442353884177 4357947893885581765413133)
                ·
                  refine ⟨1634230460207093162029925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4357947893885581765413133 1634230460207093162029925)
                  ·
                    refine ⟨306418211288829967880611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634230460207093162029925 306418211288829967880611)
                    ·
                      rfl

theorem cell23_1790242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1790242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790242 prefixEnd_1790242 := by exact prefixLift 1790242
  have htrace : WordTrace (prefixWord ++ tailWord_1790242) baseStart_1790242 baseEnd_1790242 := by
    simpa [prefixWord, tailWord_1790242, baseEnd_1790242] using wordTrace_append hprefix tailTrace_1790242
  have hstable : (prefixWord ++ tailWord_1790242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790242).length < 2 ^ (prefixWord ++ tailWord_1790242).sum := by decide
  have hdescent : baseEnd_1790242 < baseStart_1790242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790276 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1790276 : Nat := 118140960795 + 1790276 * 2 ^ 59
def prefixEnd_1790276 : Nat := 4983230072969 + 3 ^ 40 * 1790276 * 2
def baseEnd_1790276 : Nat := 306424030736247590205559

theorem tailTrace_1790276 : CollatzResearch.WordTrace tailWord_1790276 prefixEnd_1790276 306424030736247590205559 := by
  unfold tailWord_1790276
  simp only [CollatzResearch.WordTrace]
  refine ⟨32648365031071640821763341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43531153374762187762351121 32648365031071640821763341)
  ·
    refine ⟨12243136886651865308161253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32648365031071640821763341 12243136886651865308161253)
    ·
      refine ⟨2295588166247224745280235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12243136886651865308161253 2295588166247224745280235)
      ·
        refine ⟨3443382249370837117920353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295588166247224745280235 3443382249370837117920353)
        ·
          refine ⟨2582536687028127838440265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443382249370837117920353 2582536687028127838440265)
          ·
            refine ⟨1936902515271095878830199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582536687028127838440265 1936902515271095878830199)
            ·
              refine ⟨2905353772906643818245299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936902515271095878830199 2905353772906643818245299)
              ·
                refine ⟨4358030659359965727367949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905353772906643818245299 4358030659359965727367949)
                ·
                  refine ⟨1634261497259987147762981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4358030659359965727367949 1634261497259987147762981)
                  ·
                    refine ⟨306424030736247590205559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634261497259987147762981 306424030736247590205559)
                    ·
                      rfl

theorem cell23_1790276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1790276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790276 prefixEnd_1790276 := by exact prefixLift 1790276
  have htrace : WordTrace (prefixWord ++ tailWord_1790276) baseStart_1790276 baseEnd_1790276 := by
    simpa [prefixWord, tailWord_1790276, baseEnd_1790276] using wordTrace_append hprefix tailTrace_1790276
  have hstable : (prefixWord ++ tailWord_1790276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790276).length < 2 ^ (prefixWord ++ tailWord_1790276).sum := by decide
  have hdescent : baseEnd_1790276 < baseStart_1790276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790309 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_1790309 : Nat := 118140960795 + 1790309 * 2 ^ 59
def prefixEnd_1790309 : Nat := 4983230072969 + 3 ^ 40 * 1790309 * 2
def baseEnd_1790309 : Nat := 919289037070341141504025

theorem tailTrace_1790309 : CollatzResearch.WordTrace tailWord_1790309 prefixEnd_1790309 919289037070341141504025 := by
  unfold tailWord_1790309
  simp only [CollatzResearch.WordTrace]
  refine ⟨65297933671023728279477981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43531955780682485519651987 65297933671023728279477981)
  ·
    refine ⟨24486725126633898104804243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65297933671023728279477981 24486725126633898104804243)
    ·
      refine ⟨36730087689950847157206365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24486725126633898104804243 36730087689950847157206365)
      ·
        refine ⟨13773782883731567683952387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36730087689950847157206365 13773782883731567683952387)
        ·
          refine ⟨20660674325597351525928581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773782883731567683952387 20660674325597351525928581)
          ·
            refine ⟨3873876436049503411111609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20660674325597351525928581 3873876436049503411111609)
            ·
              refine ⟨2905407327037127558333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873876436049503411111609 2905407327037127558333707)
              ·
                refine ⟨4358110990555691337500561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905407327037127558333707 4358110990555691337500561)
                ·
                  refine ⟨3268583242916768503125421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358110990555691337500561 3268583242916768503125421)
                  ·
                    refine ⟨1225718716093788188672033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268583242916768503125421 1225718716093788188672033)
                    ·
                      refine ⟨919289037070341141504025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225718716093788188672033 919289037070341141504025)
                      ·
                        rfl

theorem cell23_1790309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_1790309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790309 prefixEnd_1790309 := by exact prefixLift 1790309
  have htrace : WordTrace (prefixWord ++ tailWord_1790309) baseStart_1790309 baseEnd_1790309 := by
    simpa [prefixWord, tailWord_1790309, baseEnd_1790309] using wordTrace_append hprefix tailTrace_1790309
  have hstable : (prefixWord ++ tailWord_1790309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790309).length < 2 ^ (prefixWord ++ tailWord_1790309).sum := by decide
  have hdescent : baseEnd_1790309 < baseStart_1790309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790333 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_1790333 : Nat := 118140960795 + 1790333 * 2 ^ 59
def prefixEnd_1790333 : Nat := 4983230072969 + 3 ^ 40 * 1790333 * 2
def baseEnd_1790333 : Nat := 919301360606049047603915

theorem tailTrace_1790333 : CollatzResearch.WordTrace tailWord_1790333 prefixEnd_1790333 919301360606049047603915 := by
  unfold tailWord_1790333
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298809022936780378351653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43532539348624520252234435 65298809022936780378351653)
  ·
    refine ⟨12243526691800646320940935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65298809022936780378351653 12243526691800646320940935)
    ·
      refine ⟨18365290037700969481411403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243526691800646320940935 18365290037700969481411403)
      ·
        refine ⟨27547935056551454222117105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365290037700969481411403 27547935056551454222117105)
        ·
          refine ⟨20660951292413590666587829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27547935056551454222117105 20660951292413590666587829)
          ·
            refine ⟨1936964183663774124992609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20660951292413590666587829 1936964183663774124992609)
            ·
              refine ⟨1452723137747830593744457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936964183663774124992609 1452723137747830593744457)
              ·
                refine ⟨1089542353310872945308343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452723137747830593744457 1089542353310872945308343)
                ·
                  refine ⟨1634313529966309417962515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089542353310872945308343 1634313529966309417962515)
                  ·
                    refine ⟨2451470294949464126943773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634313529966309417962515 2451470294949464126943773)
                    ·
                      refine ⟨919301360606049047603915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451470294949464126943773 919301360606049047603915)
                      ·
                        rfl

theorem cell23_1790333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_1790333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790333 prefixEnd_1790333 := by exact prefixLift 1790333
  have htrace : WordTrace (prefixWord ++ tailWord_1790333) baseStart_1790333 baseEnd_1790333 := by
    simpa [prefixWord, tailWord_1790333, baseEnd_1790333] using wordTrace_append hprefix tailTrace_1790333
  have hstable : (prefixWord ++ tailWord_1790333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790333).length < 2 ^ (prefixWord ++ tailWord_1790333).sum := by decide
  have hdescent : baseEnd_1790333 < baseStart_1790333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790345 : List Nat := [1, 2, 1, 1, 6, 1, 3, 8]
def baseStart_1790345 : Nat := 118140960795 + 1790345 * 2 ^ 59
def prefixEnd_1790345 : Nat := 4983230072969 + 3 ^ 40 * 1790345 * 2
def baseEnd_1790345 : Nat := 34048426754589000024217

theorem tailTrace_1790345 : CollatzResearch.WordTrace tailWord_1790345 prefixEnd_1790345 34048426754589000024217 := by
  unfold tailWord_1790345
  simp only [CollatzResearch.WordTrace]
  refine ⟨65299246698893306427788489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43532831132595537618525659 65299246698893306427788489)
  ·
    refine ⟨48974435024169979820841367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65299246698893306427788489 48974435024169979820841367)
    ·
      refine ⟨73461652536254969731262051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48974435024169979820841367 73461652536254969731262051)
      ·
        refine ⟨110192478804382454596893077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73461652536254969731262051 110192478804382454596893077)
        ·
          refine ⟨5165272443955427559229363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110192478804382454596893077 5165272443955427559229363)
          ·
            refine ⟨7747908665933141338844045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165272443955427559229363 7747908665933141338844045)
            ·
              refine ⟨2905465749724928002066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7747908665933141338844045 2905465749724928002066517)
              ·
                refine ⟨34048426754589000024217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2905465749724928002066517 34048426754589000024217)
                ·
                  rfl

theorem cell23_1790345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 8].length) (baseStart_1790345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790345 prefixEnd_1790345 := by exact prefixLift 1790345
  have htrace : WordTrace (prefixWord ++ tailWord_1790345) baseStart_1790345 baseEnd_1790345 := by
    simpa [prefixWord, tailWord_1790345, baseEnd_1790345] using wordTrace_append hprefix tailTrace_1790345
  have hstable : (prefixWord ++ tailWord_1790345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790345).length < 2 ^ (prefixWord ++ tailWord_1790345).sum := by decide
  have hdescent : baseEnd_1790345 < baseStart_1790345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790362 : List Nat := [3, 1, 1, 4, 1, 3, 3, 7]
def baseStart_1790362 : Nat := 118140960795 + 1790362 * 2 ^ 59
def prefixEnd_1790362 : Nat := 4983230072969 + 3 ^ 40 * 1790362 * 2
def baseEnd_1790362 : Nat := 34048750057223312375603

theorem tailTrace_1790362 : CollatzResearch.WordTrace tailWord_1790362 prefixEnd_1790362 34048750057223312375603 := by
  unfold tailWord_1790362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324966684957929582789335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43533244493221145554104893 16324966684957929582789335)
  ·
    refine ⟨24487450027436894374184003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16324966684957929582789335 24487450027436894374184003)
    ·
      refine ⟨36731175041155341561276005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24487450027436894374184003 36731175041155341561276005)
      ·
        refine ⟨6887095320216626542739251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36731175041155341561276005 6887095320216626542739251)
        ·
          refine ⟨10330642980324939814108877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887095320216626542739251 10330642980324939814108877)
          ·
            refine ⟨3873991117621852430290829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10330642980324939814108877 3873991117621852430290829)
            ·
              refine ⟨1452746669108194661359061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3873991117621852430290829 1452746669108194661359061)
              ·
                refine ⟨34048750057223312375603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1452746669108194661359061 34048750057223312375603)
                ·
                  rfl

theorem cell23_1790362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_1790362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790362 prefixEnd_1790362 := by exact prefixLift 1790362
  have htrace : WordTrace (prefixWord ++ tailWord_1790362) baseStart_1790362 baseEnd_1790362 := by
    simpa [prefixWord, tailWord_1790362, baseEnd_1790362] using wordTrace_append hprefix tailTrace_1790362
  have hstable : (prefixWord ++ tailWord_1790362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790362).length < 2 ^ (prefixWord ++ tailWord_1790362).sum := by decide
  have hdescent : baseEnd_1790362 < baseStart_1790362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790372 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1790372 : Nat := 118140960795 + 1790372 * 2 ^ 59
def prefixEnd_1790372 : Nat := 4983230072969 + 3 ^ 40 * 1790372 * 2
def baseEnd_1790372 : Nat := 919321386351574395016235

theorem tailTrace_1790372 : CollatzResearch.WordTrace tailWord_1790372 prefixEnd_1790372 919321386351574395016235 := by
  unfold tailWord_1790372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650115734897745019510685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43533487646530326692680913 32650115734897745019510685)
  ·
    refine ⟨12243793400586654382316507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32650115734897745019510685 12243793400586654382316507)
    ·
      refine ⟨18365690100879981573474761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243793400586654382316507 18365690100879981573474761)
      ·
        refine ⟨13774267575659986180106071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18365690100879981573474761 13774267575659986180106071)
        ·
          refine ⟨20661401363489979270159107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13774267575659986180106071 20661401363489979270159107)
          ·
            refine ⟨30992102045234968905238661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20661401363489979270159107 30992102045234968905238661)
            ·
              refine ⟨5811019133481556669732249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30992102045234968905238661 5811019133481556669732249)
              ·
                refine ⟨4358264350111167502299187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811019133481556669732249 4358264350111167502299187)
                ·
                  refine ⟨6537396525166751253448781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358264350111167502299187 6537396525166751253448781)
                  ·
                    refine ⟨2451523696937531720043293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6537396525166751253448781 2451523696937531720043293)
                    ·
                      refine ⟨919321386351574395016235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451523696937531720043293 919321386351574395016235)
                      ·
                        rfl

theorem cell23_1790372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1790372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790372 prefixEnd_1790372 := by exact prefixLift 1790372
  have htrace : WordTrace (prefixWord ++ tailWord_1790372) baseStart_1790372 baseEnd_1790372 := by
    simpa [prefixWord, tailWord_1790372, baseEnd_1790372] using wordTrace_append hprefix tailTrace_1790372
  have hstable : (prefixWord ++ tailWord_1790372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790372).length < 2 ^ (prefixWord ++ tailWord_1790372).sum := by decide
  have hdescent : baseEnd_1790372 < baseStart_1790372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790376 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1790376 : Nat := 118140960795 + 1790376 * 2 ^ 59
def prefixEnd_1790376 : Nat := 4983230072969 + 3 ^ 40 * 1790376 * 2
def baseEnd_1790376 : Nat := 919323440274192379366217

theorem tailTrace_1790376 : CollatzResearch.WordTrace tailWord_1790376 prefixEnd_1790376 919323440274192379366217 := by
  unfold tailWord_1790376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650188680890499361083491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43533584907853999148111321 32650188680890499361083491)
  ·
    refine ⟨48975283021335749041625237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32650188680890499361083491 48975283021335749041625237)
    ·
      refine ⟨2295716391625113236326183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48975283021335749041625237 2295716391625113236326183)
      ·
        refine ⟨3443574587437669854489275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295716391625113236326183 3443574587437669854489275)
        ·
          refine ⟨5165361881156504781733913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443574587437669854489275 5165361881156504781733913)
          ·
            refine ⟨3874021410867378586300435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165361881156504781733913 3874021410867378586300435)
            ·
              refine ⟨5811032116301067879450653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874021410867378586300435 5811032116301067879450653)
              ·
                refine ⟨2179137043612900454793995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5811032116301067879450653 2179137043612900454793995)
                ·
                  refine ⟨3268705565419350682190993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179137043612900454793995 3268705565419350682190993)
                  ·
                    refine ⟨2451529174064513011643245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268705565419350682190993 2451529174064513011643245)
                    ·
                      refine ⟨919323440274192379366217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451529174064513011643245 919323440274192379366217)
                      ·
                        rfl

theorem cell23_1790376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1790376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790376 prefixEnd_1790376 := by exact prefixLift 1790376
  have htrace : WordTrace (prefixWord ++ tailWord_1790376) baseStart_1790376 baseEnd_1790376 := by
    simpa [prefixWord, tailWord_1790376, baseEnd_1790376] using wordTrace_append hprefix tailTrace_1790376
  have hstable : (prefixWord ++ tailWord_1790376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790376).length < 2 ^ (prefixWord ++ tailWord_1790376).sum := by decide
  have hdescent : baseEnd_1790376 < baseStart_1790376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790415 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_1790415 : Nat := 118140960795 + 1790415 * 2 ^ 59
def prefixEnd_1790415 : Nat := 4983230072969 + 3 ^ 40 * 1790415 * 2
def baseEnd_1790415 : Nat := 919343466019717726778537

theorem tailTrace_1790415 : CollatzResearch.WordTrace tailWord_1790415 prefixEnd_1790415 919343466019717726778537 := by
  unfold tailWord_1790415
  simp only [CollatzResearch.WordTrace]
  refine ⟨65301799808639708382836699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43534533205759805588557799 65301799808639708382836699)
  ·
    refine ⟨97952699712959562574255049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65301799808639708382836699 97952699712959562574255049)
    ·
      refine ⟨73464524784719671930691287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97952699712959562574255049 73464524784719671930691287)
      ·
        refine ⟨110196787177079507896036931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73464524784719671930691287 110196787177079507896036931)
        ·
          refine ⟨165295180765619261844055397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110196787177079507896036931 165295180765619261844055397)
          ·
            refine ⟨30992846393553611595760387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165295180765619261844055397 30992846393553611595760387)
            ·
              refine ⟨46489269590330417393640581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992846393553611595760387 46489269590330417393640581)
              ·
                refine ⟨8716738048186953261307609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46489269590330417393640581 8716738048186953261307609)
                ·
                  refine ⟨6537553536140214945980707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716738048186953261307609 6537553536140214945980707)
                  ·
                    refine ⟨9806330304210322418971061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537553536140214945980707 9806330304210322418971061)
                    ·
                      refine ⟨919343466019717726778537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9806330304210322418971061 919343466019717726778537)
                      ·
                        rfl

theorem cell23_1790415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_1790415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790415 prefixEnd_1790415 := by exact prefixLift 1790415
  have htrace : WordTrace (prefixWord ++ tailWord_1790415) baseStart_1790415 baseEnd_1790415 := by
    simpa [prefixWord, tailWord_1790415, baseEnd_1790415] using wordTrace_append hprefix tailTrace_1790415
  have hstable : (prefixWord ++ tailWord_1790415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790415).length < 2 ^ (prefixWord ++ tailWord_1790415).sum := by decide
  have hdescent : baseEnd_1790415 < baseStart_1790415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790429 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1790429 : Nat := 118140960795 + 1790429 * 2 ^ 59
def prefixEnd_1790429 : Nat := 4983230072969 + 3 ^ 40 * 1790429 * 2
def baseEnd_1790429 : Nat := 919350654748880672003473

theorem tailTrace_1790429 : CollatzResearch.WordTrace tailWord_1790429 prefixEnd_1790429 919350654748880672003473 := by
  unfold tailWord_1790429
  simp only [CollatzResearch.WordTrace]
  refine ⟨65302310430588988773846341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43534873620392659182564227 65302310430588988773846341)
  ·
    refine ⟨12244183205735435395096189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65302310430588988773846341 12244183205735435395096189)
    ·
      refine ⟨4591568702150788273161071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12244183205735435395096189 4591568702150788273161071)
      ·
        refine ⟨6887353053226182409741607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591568702150788273161071 6887353053226182409741607)
        ·
          refine ⟨10331029579839273614612411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887353053226182409741607 10331029579839273614612411)
          ·
            refine ⟨15496544369758910421918617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10331029579839273614612411 15496544369758910421918617)
            ·
              refine ⟨11622408277319182816438963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15496544369758910421918617 11622408277319182816438963)
              ·
                refine ⟨17433612415978774224658445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622408277319182816438963 17433612415978774224658445)
                ·
                  refine ⟨6537604655992040334246917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17433612415978774224658445 6537604655992040334246917)
                  ·
                    refine ⟨1225800872998507562671297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537604655992040334246917 1225800872998507562671297)
                    ·
                      refine ⟨919350654748880672003473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225800872998507562671297 919350654748880672003473)
                      ·
                        rfl

theorem cell23_1790429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1790429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790429 prefixEnd_1790429 := by exact prefixLift 1790429
  have htrace : WordTrace (prefixWord ++ tailWord_1790429) baseStart_1790429 baseEnd_1790429 := by
    simpa [prefixWord, tailWord_1790429, baseEnd_1790429] using wordTrace_append hprefix tailTrace_1790429
  have hstable : (prefixWord ++ tailWord_1790429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790429).length < 2 ^ (prefixWord ++ tailWord_1790429).sum := by decide
  have hdescent : baseEnd_1790429 < baseStart_1790429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790446 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_1790446 : Nat := 118140960795 + 1790446 * 2 ^ 59
def prefixEnd_1790446 : Nat := 4983230072969 + 3 ^ 40 * 1790446 * 2
def baseEnd_1790446 : Nat := 919359383920007105490895

theorem tailTrace_1790446 : CollatzResearch.WordTrace tailWord_1790446 prefixEnd_1790446 919359383920007105490895 := by
  unfold tailWord_1790446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162866308940925084651899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43535286981018267118143461 8162866308940925084651899)
  ·
    refine ⟨12244299463411387626977849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162866308940925084651899 12244299463411387626977849)
    ·
      refine ⟨9183224597558540720233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12244299463411387626977849 9183224597558540720233387)
      ·
        refine ⟨13774836896337811080350081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183224597558540720233387 13774836896337811080350081)
        ·
          refine ⟨10331127672253358310262561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13774836896337811080350081 10331127672253358310262561)
          ·
            refine ⟨7748345754190018732696921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331127672253358310262561 7748345754190018732696921)
            ·
              refine ⟨5811259315642514049522691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748345754190018732696921 5811259315642514049522691)
              ·
                refine ⟨8716888973463771074284037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811259315642514049522691 8716888973463771074284037)
                ·
                  refine ⟨1634416682524457076428257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8716888973463771074284037 1634416682524457076428257)
                  ·
                    refine ⟨1225812511893342807321193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1634416682524457076428257 1225812511893342807321193)
                    ·
                      refine ⟨919359383920007105490895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225812511893342807321193 919359383920007105490895)
                      ·
                        rfl

theorem cell23_1790446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_1790446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790446 prefixEnd_1790446 := by exact prefixLift 1790446
  have htrace : WordTrace (prefixWord ++ tailWord_1790446) baseStart_1790446 baseEnd_1790446 := by
    simpa [prefixWord, tailWord_1790446, baseEnd_1790446] using wordTrace_append hprefix tailTrace_1790446
  have hstable : (prefixWord ++ tailWord_1790446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790446).length < 2 ^ (prefixWord ++ tailWord_1790446).sum := by decide
  have hdescent : baseEnd_1790446 < baseStart_1790446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790492 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1790492 : Nat := 118140960795 + 1790492 * 2 ^ 59
def prefixEnd_1790492 : Nat := 4983230072969 + 3 ^ 40 * 1790492 * 2
def baseEnd_1790492 : Nat := 919383004030113925515683

theorem tailTrace_1790492 : CollatzResearch.WordTrace tailWord_1790492 prefixEnd_1790492 919383004030113925515683 := by
  unfold tailWord_1790492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652304114680375266694865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43536405486240500355593153 32652304114680375266694865)
  ·
    refine ⟨24489228086010281450021149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32652304114680375266694865 24489228086010281450021149)
    ·
      refine ⟨9183460532253855543757931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24489228086010281450021149 9183460532253855543757931)
      ·
        refine ⟨13775190798380783315636897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183460532253855543757931 13775190798380783315636897)
        ·
          refine ⟨10331393098785587486727673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13775190798380783315636897 10331393098785587486727673)
          ·
            refine ⟨7748544824089190615045755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331393098785587486727673 7748544824089190615045755)
            ·
              refine ⟨11622817236133785922568633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748544824089190615045755 11622817236133785922568633)
              ·
                refine ⟨8717112927100339441926475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11622817236133785922568633 8717112927100339441926475)
                ·
                  refine ⟨13075669390650509162889713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717112927100339441926475 13075669390650509162889713)
                  ·
                    refine ⟨9806752042987881872167285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13075669390650509162889713 9806752042987881872167285)
                    ·
                      refine ⟨919383004030113925515683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9806752042987881872167285 919383004030113925515683)
                      ·
                        rfl

theorem cell23_1790492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1790492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790492 prefixEnd_1790492 := by exact prefixLift 1790492
  have htrace : WordTrace (prefixWord ++ tailWord_1790492) baseStart_1790492 baseEnd_1790492 := by
    simpa [prefixWord, tailWord_1790492, baseEnd_1790492] using wordTrace_append hprefix tailTrace_1790492
  have hstable : (prefixWord ++ tailWord_1790492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790492).length < 2 ^ (prefixWord ++ tailWord_1790492).sum := by decide
  have hdescent : baseEnd_1790492 < baseStart_1790492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790503 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 5]
def baseStart_1790503 : Nat := 118140960795 + 1790503 * 2 ^ 59
def prefixEnd_1790503 : Nat := 4983230072969 + 3 ^ 40 * 1790503 * 2
def baseEnd_1790503 : Nat := 102154294701923709164237

theorem tailTrace_1790503 : CollatzResearch.WordTrace tailWord_1790503 prefixEnd_1790503 102154294701923709164237 := by
  unfold tailWord_1790503
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305009432320899412040163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43536672954880599608026775 65305009432320899412040163)
  ·
    refine ⟨97957514148481349118060245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65305009432320899412040163 97957514148481349118060245)
    ·
      refine ⟨2295879237855031619954537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 97957514148481349118060245 2295879237855031619954537)
      ·
        refine ⟨1721909428391273714965903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295879237855031619954537 1721909428391273714965903)
        ·
          refine ⟨2582864142586910572448855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721909428391273714965903 2582864142586910572448855)
          ·
            refine ⟨3874296213880365858673283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582864142586910572448855 3874296213880365858673283)
            ·
              refine ⟨5811444320820548788009925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874296213880365858673283 5811444320820548788009925)
              ·
                refine ⟨1089645810153852897751861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5811444320820548788009925 1089645810153852897751861)
                ·
                  refine ⟨102154294701923709164237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089645810153852897751861 102154294701923709164237)
                  ·
                    rfl

theorem cell23_1790503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 5].length) (baseStart_1790503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790503 prefixEnd_1790503 := by exact prefixLift 1790503
  have htrace : WordTrace (prefixWord ++ tailWord_1790503) baseStart_1790503 baseEnd_1790503 := by
    simpa [prefixWord, tailWord_1790503, baseEnd_1790503] using wordTrace_append hprefix tailTrace_1790503
  have hstable : (prefixWord ++ tailWord_1790503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790503).length < 2 ^ (prefixWord ++ tailWord_1790503).sum := by decide
  have hdescent : baseEnd_1790503 < baseStart_1790503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790519 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_1790519 : Nat := 118140960795 + 1790519 * 2 ^ 59
def prefixEnd_1790519 : Nat := 4983230072969 + 3 ^ 40 * 1790519 * 2
def baseEnd_1790519 : Nat := 919396868007785319878059

theorem tailTrace_1790519 : CollatzResearch.WordTrace tailWord_1790519 prefixEnd_1790519 919396868007785319878059 := by
  unfold tailWord_1790519
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305593000262934144622611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43537062000175289429748407 65305593000262934144622611)
  ·
    refine ⟨97958389500394401216933917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65305593000262934144622611 97958389500394401216933917)
    ·
      refine ⟨36734396062647900456350219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97958389500394401216933917 36734396062647900456350219)
      ·
        refine ⟨55101594093971850684525329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36734396062647900456350219 55101594093971850684525329)
        ·
          refine ⟨41326195570478888013393997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55101594093971850684525329 41326195570478888013393997)
          ·
            refine ⟨15497323338929583005022749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41326195570478888013393997 15497323338929583005022749)
            ·
              refine ⟨5811496252098593626883531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15497323338929583005022749 5811496252098593626883531)
              ·
                refine ⟨8717244378147890440325297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811496252098593626883531 8717244378147890440325297)
                ·
                  refine ⟨6537933283610917830243973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8717244378147890440325297 6537933283610917830243973)
                  ·
                    refine ⟨1225862490677047093170745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537933283610917830243973 1225862490677047093170745)
                    ·
                      refine ⟨919396868007785319878059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225862490677047093170745 919396868007785319878059)
                      ·
                        rfl

theorem cell23_1790519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_1790519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790519 prefixEnd_1790519 := by exact prefixLift 1790519
  have htrace : WordTrace (prefixWord ++ tailWord_1790519) baseStart_1790519 baseEnd_1790519 := by
    simpa [prefixWord, tailWord_1790519, baseEnd_1790519] using wordTrace_append hprefix tailTrace_1790519
  have hstable : (prefixWord ++ tailWord_1790519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790519).length < 2 ^ (prefixWord ++ tailWord_1790519).sum := by decide
  have hdescent : baseEnd_1790519 < baseStart_1790519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790529 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1790529 : Nat := 118140960795 + 1790529 * 2 ^ 59
def prefixEnd_1790529 : Nat := 4983230072969 + 3 ^ 40 * 1790529 * 2
def baseEnd_1790529 : Nat := 306467334271443426917671

theorem tailTrace_1790529 : CollatzResearch.WordTrace tailWord_1790529 prefixEnd_1790529 306467334271443426917671 := by
  unfold tailWord_1790529
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305957730226705852486641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43537305153484470568324427 65305957730226705852486641)
  ·
    refine ⟨48979468297670029389364981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65305957730226705852486641 48979468297670029389364981)
    ·
      refine ⟨4591825152906565255252967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48979468297670029389364981 4591825152906565255252967)
      ·
        refine ⟨6887737729359847882879451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591825152906565255252967 6887737729359847882879451)
        ·
          refine ⟨10331606594039771824319177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887737729359847882879451 10331606594039771824319177)
          ·
            refine ⟨7748704945529828868239383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331606594039771824319177 7748704945529828868239383)
            ·
              refine ⟨11623057418294743302359075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748704945529828868239383 11623057418294743302359075)
              ·
                refine ⟨17434586127442114953538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623057418294743302359075 17434586127442114953538613)
                ·
                  refine ⟨1634492449447698276894245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17434586127442114953538613 1634492449447698276894245)
                  ·
                    refine ⟨306467334271443426917671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634492449447698276894245 306467334271443426917671)
                    ·
                      rfl

theorem cell23_1790529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1790529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790529 prefixEnd_1790529 := by exact prefixLift 1790529
  have htrace : WordTrace (prefixWord ++ tailWord_1790529) baseStart_1790529 baseEnd_1790529 := by
    simpa [prefixWord, tailWord_1790529, baseEnd_1790529] using wordTrace_append hprefix tailTrace_1790529
  have hstable : (prefixWord ++ tailWord_1790529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790529).length < 2 ^ (prefixWord ++ tailWord_1790529).sum := by decide
  have hdescent : baseEnd_1790529 < baseStart_1790529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790539 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3]
def baseStart_1790539 : Nat := 118140960795 + 1790539 * 2 ^ 59
def prefixEnd_1790539 : Nat := 4983230072969 + 3 ^ 40 * 1790539 * 2
def baseEnd_1790539 : Nat := 919407137620875241627967

theorem tailTrace_1790539 : CollatzResearch.WordTrace tailWord_1790539 prefixEnd_1790539 919407137620875241627967 := by
  unfold tailWord_1790539
  simp only [CollatzResearch.WordTrace]
  refine ⟨65306322460190477560350671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43537548306793651706900447 65306322460190477560350671)
  ·
    refine ⟨97959483690285716340526007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65306322460190477560350671 97959483690285716340526007)
    ·
      refine ⟨146939225535428574510789011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97959483690285716340526007 146939225535428574510789011)
      ·
        refine ⟨220408838303142861766183517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146939225535428574510789011 220408838303142861766183517)
        ·
          refine ⟨82653314363678573162318819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220408838303142861766183517 82653314363678573162318819)
          ·
            refine ⟨123979971545517859743478229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82653314363678573162318819 123979971545517859743478229)
            ·
              refine ⟨2905780583098074837737771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123979971545517859743478229 2905780583098074837737771)
              ·
                refine ⟨4358670874647112256606657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905780583098074837737771 4358670874647112256606657)
                ·
                  refine ⟨3269003155985334192454993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358670874647112256606657 3269003155985334192454993)
                  ·
                    refine ⟨2451752366989000644341245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3269003155985334192454993 2451752366989000644341245)
                    ·
                      refine ⟨919407137620875241627967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451752366989000644341245 919407137620875241627967)
                      ·
                        rfl

theorem cell23_1790539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].length) (baseStart_1790539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790539 prefixEnd_1790539 := by exact prefixLift 1790539
  have htrace : WordTrace (prefixWord ++ tailWord_1790539) baseStart_1790539 baseEnd_1790539 := by
    simpa [prefixWord, tailWord_1790539, baseEnd_1790539] using wordTrace_append hprefix tailTrace_1790539
  have hstable : (prefixWord ++ tailWord_1790539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790539).length < 2 ^ (prefixWord ++ tailWord_1790539).sum := by decide
  have hdescent : baseEnd_1790539 < baseStart_1790539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790572 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_1790572 : Nat := 118140960795 + 1790572 * 2 ^ 59
def prefixEnd_1790572 : Nat := 4983230072969 + 3 ^ 40 * 1790572 * 2
def baseEnd_1790572 : Nat := 306474694160824537505105

theorem tailTrace_1790572 : CollatzResearch.WordTrace tailWord_1790572 prefixEnd_1790572 306474694160824537505105 := by
  unfold tailWord_1790572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653763034535462098150985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43538350712713949464201313 32653763034535462098150985)
  ·
    refine ⟨24490322275901596573613239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32653763034535462098150985 24490322275901596573613239)
    ·
      refine ⟨36735483413852394860419859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24490322275901596573613239 36735483413852394860419859)
      ·
        refine ⟨55103225120778592290629789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36735483413852394860419859 55103225120778592290629789)
        ·
          refine ⟨20663709420291972108986171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55103225120778592290629789 20663709420291972108986171)
          ·
            refine ⟨30995564130437958163479257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20663709420291972108986171 30995564130437958163479257)
            ·
              refine ⟨23246673097828468622609443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30995564130437958163479257 23246673097828468622609443)
              ·
                refine ⟨34870009646742702933914165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23246673097828468622609443 34870009646742702933914165)
                ·
                  refine ⟨3269063404382128400054453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34870009646742702933914165 3269063404382128400054453)
                  ·
                    refine ⟨306474694160824537505105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3269063404382128400054453 306474694160824537505105)
                    ·
                      rfl

theorem cell23_1790572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_1790572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790572 prefixEnd_1790572 := by exact prefixLift 1790572
  have htrace : WordTrace (prefixWord ++ tailWord_1790572) baseStart_1790572 baseEnd_1790572 := by
    simpa [prefixWord, tailWord_1790572, baseEnd_1790572] using wordTrace_append hprefix tailTrace_1790572
  have hstable : (prefixWord ++ tailWord_1790572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790572).length < 2 ^ (prefixWord ++ tailWord_1790572).sum := by decide
  have hdescent : baseEnd_1790572 < baseStart_1790572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790576 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 6]
def baseStart_1790576 : Nat := 118140960795 + 1790576 * 2 ^ 59
def prefixEnd_1790576 : Nat := 4983230072969 + 3 ^ 40 * 1790576 * 2
def baseEnd_1790576 : Nat := 102158459600565732985033

theorem tailTrace_1790576 : CollatzResearch.WordTrace tailWord_1790576 prefixEnd_1790576 102158459600565732985033 := by
  unfold tailWord_1790576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653835980528216439723791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43538447974037621919631721 32653835980528216439723791)
  ·
    refine ⟨48980753970792324659585687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32653835980528216439723791 48980753970792324659585687)
    ·
      refine ⟨73471130956188486989378531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48980753970792324659585687 73471130956188486989378531)
      ·
        refine ⟨110206696434282730484067797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73471130956188486989378531 110206696434282730484067797)
        ·
          refine ⟨2582969447678501495720339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110206696434282730484067797 2582969447678501495720339)
          ·
            refine ⟨3874454171517752243580509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582969447678501495720339 3874454171517752243580509)
            ·
              refine ⟨1452920314319157091342691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3874454171517752243580509 1452920314319157091342691)
              ·
                refine ⟨2179380471478735637014037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452920314319157091342691 2179380471478735637014037)
                ·
                  refine ⟨102158459600565732985033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2179380471478735637014037 102158459600565732985033)
                  ·
                    rfl

theorem cell23_1790576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_1790576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790576 prefixEnd_1790576 := by exact prefixLift 1790576
  have htrace : WordTrace (prefixWord ++ tailWord_1790576) baseStart_1790576 baseEnd_1790576 := by
    simpa [prefixWord, tailWord_1790576, baseEnd_1790576] using wordTrace_append hprefix tailTrace_1790576
  have hstable : (prefixWord ++ tailWord_1790576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790576).length < 2 ^ (prefixWord ++ tailWord_1790576).sum := by decide
  have hdescent : baseEnd_1790576 < baseStart_1790576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790579 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 6, 3, 2]
def baseStart_1790579 : Nat := 118140960795 + 1790579 * 2 ^ 59
def prefixEnd_1790579 : Nat := 4983230072969 + 3 ^ 40 * 1790579 * 2
def baseEnd_1790579 : Nat := 919427676847055085127783

theorem tailTrace_1790579 : CollatzResearch.WordTrace tailWord_1790579 prefixEnd_1790579 919427676847055085127783 := by
  unfold tailWord_1790579
  simp only [CollatzResearch.WordTrace]
  refine ⟨65307781380045564391806791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43538520920030376261204527 65307781380045564391806791)
  ·
    refine ⟨97961672070068346587710187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65307781380045564391806791 97961672070068346587710187)
    ·
      refine ⟨146942508105102519881565281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97961672070068346587710187 146942508105102519881565281)
      ·
        refine ⟨110206881078826889911173961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146942508105102519881565281 110206881078826889911173961)
        ·
          refine ⟨82655160809120167433380471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110206881078826889911173961 82655160809120167433380471)
          ·
            refine ⟨123982741213680251150070707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82655160809120167433380471 123982741213680251150070707)
            ·
              refine ⟨185974111820520376725106061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123982741213680251150070707 185974111820520376725106061)
              ·
                refine ⟨69740291932695141271914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185974111820520376725106061 69740291932695141271914773)
                ·
                  refine ⟨3269076184345084747121005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69740291932695141271914773 3269076184345084747121005)
                  ·
                    refine ⟨1225903569129406780170377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269076184345084747121005 1225903569129406780170377)
                    ·
                      refine ⟨919427676847055085127783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225903569129406780170377 919427676847055085127783)
                      ·
                        rfl

theorem cell23_1790579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3, 2].length) (baseStart_1790579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790579 prefixEnd_1790579 := by exact prefixLift 1790579
  have htrace : WordTrace (prefixWord ++ tailWord_1790579) baseStart_1790579 baseEnd_1790579 := by
    simpa [prefixWord, tailWord_1790579, baseEnd_1790579] using wordTrace_append hprefix tailTrace_1790579
  have hstable : (prefixWord ++ tailWord_1790579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790579).length < 2 ^ (prefixWord ++ tailWord_1790579).sum := by decide
  have hdescent : baseEnd_1790579 < baseStart_1790579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790596 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1790596 : Nat := 118140960795 + 1790596 * 2 ^ 59
def prefixEnd_1790596 : Nat := 4983230072969 + 3 ^ 40 * 1790596 * 2
def baseEnd_1790596 : Nat := 919436406018181518615205

theorem tailTrace_1790596 : CollatzResearch.WordTrace tailWord_1790596 prefixEnd_1790596 919436406018181518615205 := by
  unfold tailWord_1790596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654200710491988147587821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43538934280655984196783761 32654200710491988147587821)
  ·
    refine ⟨12245325266434495555345433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32654200710491988147587821 12245325266434495555345433)
    ·
      refine ⟨9183993949825871666509075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12245325266434495555345433 9183993949825871666509075)
      ·
        refine ⟨13775990924738807499763613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183993949825871666509075 13775990924738807499763613)
        ·
          refine ⟨5165996596777052812411355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13775990924738807499763613 5165996596777052812411355)
          ·
            refine ⟨7748994895165579218617033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165996596777052812411355 7748994895165579218617033)
            ·
              refine ⟨5811746171374184413962775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748994895165579218617033 5811746171374184413962775)
              ·
                refine ⟨8717619257061276620944163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811746171374184413962775 8717619257061276620944163)
                ·
                  refine ⟨13076428885591914931416245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717619257061276620944163 13076428885591914931416245)
                  ·
                    refine ⟨1225915208024242024820273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13076428885591914931416245 1225915208024242024820273)
                    ·
                      refine ⟨919436406018181518615205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1225915208024242024820273 919436406018181518615205)
                      ·
                        rfl

theorem cell23_1790596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1790596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790596 prefixEnd_1790596 := by exact prefixLift 1790596
  have htrace : WordTrace (prefixWord ++ tailWord_1790596) baseStart_1790596 baseEnd_1790596 := by
    simpa [prefixWord, tailWord_1790596, baseEnd_1790596] using wordTrace_append hprefix tailTrace_1790596
  have hstable : (prefixWord ++ tailWord_1790596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790596).length < 2 ^ (prefixWord ++ tailWord_1790596).sum := by decide
  have hdescent : baseEnd_1790596 < baseStart_1790596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790629 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1790629 : Nat := 118140960795 + 1790629 * 2 ^ 59
def prefixEnd_1790629 : Nat := 4983230072969 + 3 ^ 40 * 1790629 * 2
def baseEnd_1790629 : Nat := 919453350879779889502553

theorem tailTrace_1790629 : CollatzResearch.WordTrace tailWord_1790629 prefixEnd_1790629 919453350879779889502553 := by
  unfold tailWord_1790629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65309605029864422931126941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43539736686576281954084627 65309605029864422931126941)
  ·
    refine ⟨24491101886199158599172603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65309605029864422931126941 24491101886199158599172603)
    ·
      refine ⟨36736652829298737898758905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24491101886199158599172603 36736652829298737898758905)
      ·
        refine ⟨27552489621974053424069179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36736652829298737898758905 27552489621974053424069179)
        ·
          refine ⟨41328734432961080136103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27552489621974053424069179 41328734432961080136103769)
          ·
            refine ⟨30996550824720810102077827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41328734432961080136103769 30996550824720810102077827)
            ·
              refine ⟨46494826237081215153116741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30996550824720810102077827 46494826237081215153116741)
              ·
                refine ⟨8717779919452727841209389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46494826237081215153116741 8717779919452727841209389)
                ·
                  refine ⟨3269167469794772940453521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8717779919452727841209389 3269167469794772940453521)
                  ·
                    refine ⟨2451875602346079705340141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3269167469794772940453521 2451875602346079705340141)
                    ·
                      refine ⟨919453350879779889502553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451875602346079705340141 919453350879779889502553)
                      ·
                        rfl

theorem cell23_1790629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1790629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790629 prefixEnd_1790629 := by exact prefixLift 1790629
  have htrace : WordTrace (prefixWord ++ tailWord_1790629) baseStart_1790629 baseEnd_1790629 := by
    simpa [prefixWord, tailWord_1790629, baseEnd_1790629] using wordTrace_append hprefix tailTrace_1790629
  have hstable : (prefixWord ++ tailWord_1790629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790629).length < 2 ^ (prefixWord ++ tailWord_1790629).sum := by decide
  have hdescent : baseEnd_1790629 < baseStart_1790629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790672 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1790672 : Nat := 118140960795 + 1790672 * 2 ^ 59
def prefixEnd_1790672 : Nat := 4983230072969 + 3 ^ 40 * 1790672 * 2
def baseEnd_1790672 : Nat := 919475430547923221264855

theorem tailTrace_1790672 : CollatzResearch.WordTrace tailWord_1790672 prefixEnd_1790672 919475430547923221264855 := by
  unfold tailWord_1790672
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655586684354320637471135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43540782245805760849961513 32655586684354320637471135)
  ·
    refine ⟨48983380026531480956206703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32655586684354320637471135 48983380026531480956206703)
    ·
      refine ⟨73475070039797221434310055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48983380026531480956206703 73475070039797221434310055)
      ·
        refine ⟨110212605059695832151465083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73475070039797221434310055 110212605059695832151465083)
        ·
          refine ⟨165318907589543748227197625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110212605059695832151465083 165318907589543748227197625)
          ·
            refine ⟨123989180692157811170398219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165318907589543748227197625 123989180692157811170398219)
            ·
              refine ⟨185983771038236716755597329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123989180692157811170398219 185983771038236716755597329)
              ·
                refine ⟨139487828278677537566697997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185983771038236716755597329 139487828278677537566697997)
                ·
                  refine ⟨52307935604504076587511749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139487828278677537566697997 52307935604504076587511749)
                  ·
                    refine ⟨9807737925844514360158453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52307935604504076587511749 9807737925844514360158453)
                    ·
                      refine ⟨919475430547923221264855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9807737925844514360158453 919475430547923221264855)
                      ·
                        rfl

theorem cell23_1790672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1790672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790672 prefixEnd_1790672 := by exact prefixLift 1790672
  have htrace : WordTrace (prefixWord ++ tailWord_1790672) baseStart_1790672 baseEnd_1790672 := by
    simpa [prefixWord, tailWord_1790672, baseEnd_1790672] using wordTrace_append hprefix tailTrace_1790672
  have hstable : (prefixWord ++ tailWord_1790672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790672).length < 2 ^ (prefixWord ++ tailWord_1790672).sum := by decide
  have hdescent : baseEnd_1790672 < baseStart_1790672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790693 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1790693 : Nat := 118140960795 + 1790693 * 2 ^ 59
def prefixEnd_1790693 : Nat := 4983230072969 + 3 ^ 40 * 1790693 * 2
def baseEnd_1790693 : Nat := 919486213641667639102259

theorem tailTrace_1790693 : CollatzResearch.WordTrace tailWord_1790693 prefixEnd_1790693 919486213641667639102259 := by
  unfold tailWord_1790693
  simp only [CollatzResearch.WordTrace]
  refine ⟨65311939301632561861456733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43541292867755041240971155 65311939301632561861456733)
  ·
    refine ⟨24491977238112210698046275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65311939301632561861456733 24491977238112210698046275)
    ·
      refine ⟨36737965857168316047069413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24491977238112210698046275 36737965857168316047069413)
      ·
        refine ⟨6888368598219059258825515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36737965857168316047069413 6888368598219059258825515)
        ·
          refine ⟨10332552897328588888238273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888368598219059258825515 10332552897328588888238273)
          ·
            refine ⟨7749414672996441666178705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10332552897328588888238273 7749414672996441666178705)
            ·
              refine ⟨5812061004747331249634029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749414672996441666178705 5812061004747331249634029)
              ·
                refine ⟨2179522876780249218612761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5812061004747331249634029 2179522876780249218612761)
                ·
                  refine ⟨1634642157585186913959571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2179522876780249218612761 1634642157585186913959571)
                  ·
                    refine ⟨2451963236377780370939357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634642157585186913959571 2451963236377780370939357)
                    ·
                      refine ⟨919486213641667639102259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2451963236377780370939357 919486213641667639102259)
                      ·
                        rfl

theorem cell23_1790693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1790693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790693 prefixEnd_1790693 := by exact prefixLift 1790693
  have htrace : WordTrace (prefixWord ++ tailWord_1790693) baseStart_1790693 baseEnd_1790693 := by
    simpa [prefixWord, tailWord_1790693, baseEnd_1790693] using wordTrace_append hprefix tailTrace_1790693
  have hstable : (prefixWord ++ tailWord_1790693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790693).length < 2 ^ (prefixWord ++ tailWord_1790693).sum := by decide
  have hdescent : baseEnd_1790693 < baseStart_1790693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790729 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_1790729 : Nat := 118140960795 + 1790729 * 2 ^ 59
def prefixEnd_1790729 : Nat := 4983230072969 + 3 ^ 40 * 1790729 * 2
def baseEnd_1790729 : Nat := 919504698945229498252093

theorem tailTrace_1790729 : CollatzResearch.WordTrace tailWord_1790729 prefixEnd_1790729 919504698945229498252093 := by
  unfold tailWord_1790729
  simp only [CollatzResearch.WordTrace]
  refine ⟨65313252329502140009767241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43542168219668093339844827 65313252329502140009767241)
  ·
    refine ⟨48984939247126605007325431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65313252329502140009767241 48984939247126605007325431)
    ·
      refine ⟨73477408870689907510988147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48984939247126605007325431 73477408870689907510988147)
      ·
        refine ⟨110216113306034861266482221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73477408870689907510988147 110216113306034861266482221)
        ·
          refine ⟨41331042489763072974930833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110216113306034861266482221 41331042489763072974930833)
          ·
            refine ⟨30998281867322304731198125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41331042489763072974930833 30998281867322304731198125)
            ·
              refine ⟨11624355700245864274199297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30998281867322304731198125 11624355700245864274199297)
              ·
                refine ⟨8718266775184398205649473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11624355700245864274199297 8718266775184398205649473)
                ·
                  refine ⟨6538700081388298654237105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718266775184398205649473 6538700081388298654237105)
                  ·
                    refine ⟨4904025061041223990677829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6538700081388298654237105 4904025061041223990677829)
                    ·
                      refine ⟨919504698945229498252093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904025061041223990677829 919504698945229498252093)
                      ·
                        rfl

theorem cell23_1790729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_1790729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790729 prefixEnd_1790729 := by exact prefixLift 1790729
  have htrace : WordTrace (prefixWord ++ tailWord_1790729) baseStart_1790729 baseEnd_1790729 := by
    simpa [prefixWord, tailWord_1790729, baseEnd_1790729] using wordTrace_append hprefix tailTrace_1790729
  have hstable : (prefixWord ++ tailWord_1790729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790729).length < 2 ^ (prefixWord ++ tailWord_1790729).sum := by decide
  have hdescent : baseEnd_1790729 < baseStart_1790729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790739 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 7]
def baseStart_1790739 : Nat := 118140960795 + 1790739 * 2 ^ 59
def prefixEnd_1790739 : Nat := 4983230072969 + 3 ^ 40 * 1790739 * 2
def baseEnd_1790739 : Nat := 102167759305752717680783

theorem tailTrace_1790739 : CollatzResearch.WordTrace tailWord_1790739 prefixEnd_1790739 102167759305752717680783 := by
  unfold tailWord_1790739
  simp only [CollatzResearch.WordTrace]
  refine ⟨65313617059465911717631271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43542411372977274478420847 65313617059465911717631271)
  ·
    refine ⟨97970425589198867576446907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65313617059465911717631271 97970425589198867576446907)
    ·
      refine ⟨146955638383798301364670361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97970425589198867576446907 146955638383798301364670361)
      ·
        refine ⟨110216728787848726023502771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146955638383798301364670361 110216728787848726023502771)
        ·
          refine ⟨165325093181773089035254157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110216728787848726023502771 165325093181773089035254157)
          ·
            refine ⟨61996909943164908388220309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165325093181773089035254157 61996909943164908388220309)
            ·
              refine ⟨2906105153585855080697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61996909943164908388220309 2906105153585855080697827)
              ·
                refine ⟨4359157730378782621046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906105153585855080697827 4359157730378782621046741)
                ·
                  refine ⟨102167759305752717680783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4359157730378782621046741 102167759305752717680783)
                  ·
                    rfl

theorem cell23_1790739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 7].length) (baseStart_1790739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790739 prefixEnd_1790739 := by exact prefixLift 1790739
  have htrace : WordTrace (prefixWord ++ tailWord_1790739) baseStart_1790739 baseEnd_1790739 := by
    simpa [prefixWord, tailWord_1790739, baseEnd_1790739] using wordTrace_append hprefix tailTrace_1790739
  have hstable : (prefixWord ++ tailWord_1790739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790739).length < 2 ^ (prefixWord ++ tailWord_1790739).sum := by decide
  have hdescent : baseEnd_1790739 < baseStart_1790739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790769 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_1790769 : Nat := 118140960795 + 1790769 * 2 ^ 59
def prefixEnd_1790769 : Nat := 4983230072969 + 3 ^ 40 * 1790769 * 2
def baseEnd_1790769 : Nat := 306508412723803113917303

theorem tailTrace_1790769 : CollatzResearch.WordTrace tailWord_1790769 prefixEnd_1790769 306508412723803113917303 := by
  unfold tailWord_1790769
  simp only [CollatzResearch.WordTrace]
  refine ⟨65314711249357226841223361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43543140832904817894148907 65314711249357226841223361)
  ·
    refine ⟨48986033437017920130917521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65314711249357226841223361 48986033437017920130917521)
    ·
      refine ⟨36739525077763440098188141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48986033437017920130917521 36739525077763440098188141)
      ·
        refine ⟨13777321904161290036820553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36739525077763440098188141 13777321904161290036820553)
        ·
          refine ⟨10332991428120967527615415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777321904161290036820553 10332991428120967527615415)
          ·
            refine ⟨15499487142181451291423123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332991428120967527615415 15499487142181451291423123)
            ·
              refine ⟨23249230713272176937134685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499487142181451291423123 23249230713272176937134685)
              ·
                refine ⟨8718461517477066351425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23249230713272176937134685 8718461517477066351425507)
                ·
                  refine ⟨13077692276215599527138261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718461517477066351425507 13077692276215599527138261)
                  ·
                    refine ⟨306508412723803113917303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13077692276215599527138261 306508412723803113917303)
                    ·
                      rfl

theorem cell23_1790769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_1790769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790769 prefixEnd_1790769 := by exact prefixLift 1790769
  have htrace : WordTrace (prefixWord ++ tailWord_1790769) baseStart_1790769 baseEnd_1790769 := by
    simpa [prefixWord, tailWord_1790769, baseEnd_1790769] using wordTrace_append hprefix tailTrace_1790769
  have hstable : (prefixWord ++ tailWord_1790769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790769).length < 2 ^ (prefixWord ++ tailWord_1790769).sum := by decide
  have hdescent : baseEnd_1790769 < baseStart_1790769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790773 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 5]
def baseStart_1790773 : Nat := 118140960795 + 1790773 * 2 ^ 59
def prefixEnd_1790773 : Nat := 4983230072969 + 3 ^ 40 * 1790773 * 2
def baseEnd_1790773 : Nat := 102169699121558591789099

theorem tailTrace_1790773 : CollatzResearch.WordTrace tailWord_1790773 prefixEnd_1790773 102169699121558591789099 := by
  unfold tailWord_1790773
  simp only [CollatzResearch.WordTrace]
  refine ⟨65314857141342735524368973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43543238094228490349579315 65314857141342735524368973)
  ·
    refine ⟨24493071428003525821638365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65314857141342735524368973 24493071428003525821638365)
    ·
      refine ⟨9184901785501322183114387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24493071428003525821638365 9184901785501322183114387)
      ·
        refine ⟨13777352678251983274671581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184901785501322183114387 13777352678251983274671581)
        ·
          refine ⟨5166507254344493728001843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13777352678251983274671581 5166507254344493728001843)
          ·
            refine ⟨7749760881516740592002765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166507254344493728001843 7749760881516740592002765)
            ·
              refine ⟨2906160330568777722001037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7749760881516740592002765 2906160330568777722001037)
              ·
                refine ⟨1089810123963291645750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2906160330568777722001037 1089810123963291645750389)
                ·
                  refine ⟨102169699121558591789099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089810123963291645750389 102169699121558591789099)
                  ·
                    rfl

theorem cell23_1790773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_1790773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790773 prefixEnd_1790773 := by exact prefixLift 1790773
  have htrace : WordTrace (prefixWord ++ tailWord_1790773) baseStart_1790773 baseEnd_1790773 := by
    simpa [prefixWord, tailWord_1790773, baseEnd_1790773] using wordTrace_append hprefix tailTrace_1790773
  have hstable : (prefixWord ++ tailWord_1790773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790773).length < 2 ^ (prefixWord ++ tailWord_1790773).sum := by decide
  have hdescent : baseEnd_1790773 < baseStart_1790773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790789 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1790789 : Nat := 118140960795 + 1790789 * 2 ^ 59
def prefixEnd_1790789 : Nat := 4983230072969 + 3 ^ 40 * 1790789 * 2
def baseEnd_1790789 : Nat := 919535507784499263501817

theorem tailTrace_1790789 : CollatzResearch.WordTrace tailWord_1790789 prefixEnd_1790789 919535507784499263501817 := by
  unfold tailWord_1790789
  simp only [CollatzResearch.WordTrace]
  refine ⟨65315440709284770256951421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43543627139523180171300947 65315440709284770256951421)
  ·
    refine ⟨24493290265981788846356783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65315440709284770256951421 24493290265981788846356783)
    ·
      refine ⟨36739935398972683269535175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24493290265981788846356783 36739935398972683269535175)
      ·
        refine ⟨55109903098459024904302763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36739935398972683269535175 55109903098459024904302763)
        ·
          refine ⟨82664854647688537356454145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55109903098459024904302763 82664854647688537356454145)
          ·
            refine ⟨61998640985766403017340609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82664854647688537356454145 61998640985766403017340609)
            ·
              refine ⟨46498980739324802263005457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61998640985766403017340609 46498980739324802263005457)
              ·
                refine ⟨34874235554493601697254093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46498980739324802263005457 34874235554493601697254093)
                ·
                  refine ⟨13077838332935100636470285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34874235554493601697254093 13077838332935100636470285)
                  ·
                    refine ⟨4904189374850662738676357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13077838332935100636470285 4904189374850662738676357)
                    ·
                      refine ⟨919535507784499263501817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904189374850662738676357 919535507784499263501817)
                      ·
                        rfl

theorem cell23_1790789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1790789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790789 prefixEnd_1790789 := by exact prefixLift 1790789
  have htrace : WordTrace (prefixWord ++ tailWord_1790789) baseStart_1790789 baseEnd_1790789 := by
    simpa [prefixWord, tailWord_1790789, baseEnd_1790789] using wordTrace_append hprefix tailTrace_1790789
  have hstable : (prefixWord ++ tailWord_1790789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790789).length < 2 ^ (prefixWord ++ tailWord_1790789).sum := by decide
  have hdescent : baseEnd_1790789 < baseStart_1790789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790796 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1790796 : Nat := 118140960795 + 1790796 * 2 ^ 59
def prefixEnd_1790796 : Nat := 4983230072969 + 3 ^ 40 * 1790796 * 2
def baseEnd_1790796 : Nat := 919539102149080736114285

theorem tailTrace_1790796 : CollatzResearch.WordTrace tailWord_1790796 prefixEnd_1790796 919539102149080736114285 := by
  unfold tailWord_1790796
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657848010129705226228121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43543797346839606968304161 32657848010129705226228121)
  ·
    refine ⟨24493386007597278919671091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32657848010129705226228121 24493386007597278919671091)
    ·
      refine ⟨36740079011395918379506637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24493386007597278919671091 36740079011395918379506637)
      ·
        refine ⟨13777529629273469392314989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36740079011395918379506637 13777529629273469392314989)
        ·
          refine ⟨5166573610977551022118121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13777529629273469392314989 5166573610977551022118121)
          ·
            refine ⟨3874930208233163266588591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5166573610977551022118121 3874930208233163266588591)
            ·
              refine ⟨5812395312349744899882887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874930208233163266588591 5812395312349744899882887)
              ·
                refine ⟨8718592968524617349824331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812395312349744899882887 8718592968524617349824331)
                ·
                  refine ⟨13077889452786926024736497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718592968524617349824331 13077889452786926024736497)
                  ·
                    refine ⟨9808417089590194518552373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13077889452786926024736497 9808417089590194518552373)
                    ·
                      refine ⟨919539102149080736114285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9808417089590194518552373 919539102149080736114285)
                      ·
                        rfl

theorem cell23_1790796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1790796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790796 prefixEnd_1790796 := by exact prefixLift 1790796
  have htrace : WordTrace (prefixWord ++ tailWord_1790796) baseStart_1790796 baseEnd_1790796 := by
    simpa [prefixWord, tailWord_1790796, baseEnd_1790796] using wordTrace_append hprefix tailTrace_1790796
  have hstable : (prefixWord ++ tailWord_1790796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790796).length < 2 ^ (prefixWord ++ tailWord_1790796).sum := by decide
  have hdescent : baseEnd_1790796 < baseStart_1790796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790816 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_1790816 : Nat := 118140960795 + 1790816 * 2 ^ 59
def prefixEnd_1790816 : Nat := 4983230072969 + 3 ^ 40 * 1790816 * 2
def baseEnd_1790816 : Nat := 306516457254056885954731

theorem tailTrace_1790816 : CollatzResearch.WordTrace tailWord_1790816 prefixEnd_1790816 306516457254056885954731 := by
  unfold tailWord_1790816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658212740093476934092151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43544283653457969245456201 32658212740093476934092151)
  ·
    refine ⟨48987319110140215401138227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32658212740093476934092151 48987319110140215401138227)
    ·
      refine ⟨73480978665210323101707341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48987319110140215401138227 73480978665210323101707341)
      ·
        refine ⟨27555366999453871163140253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73480978665210323101707341 27555366999453871163140253)
        ·
          refine ⟨10333262624795201686177595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27555366999453871163140253 10333262624795201686177595)
          ·
            refine ⟨15499893937192802529266393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333262624795201686177595 15499893937192802529266393)
            ·
              refine ⟨11624920452894601896949795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15499893937192802529266393 11624920452894601896949795)
              ·
                refine ⟨17437380679341902845424693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11624920452894601896949795 17437380679341902845424693)
                ·
                  refine ⟨1634754438688303391758565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17437380679341902845424693 1634754438688303391758565)
                  ·
                    refine ⟨306516457254056885954731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634754438688303391758565 306516457254056885954731)
                    ·
                      rfl

theorem cell23_1790816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_1790816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790816 prefixEnd_1790816 := by exact prefixLift 1790816
  have htrace : WordTrace (prefixWord ++ tailWord_1790816) baseStart_1790816 baseEnd_1790816 := by
    simpa [prefixWord, tailWord_1790816, baseEnd_1790816] using wordTrace_append hprefix tailTrace_1790816
  have hstable : (prefixWord ++ tailWord_1790816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790816).length < 2 ^ (prefixWord ++ tailWord_1790816).sum := by decide
  have hdescent : baseEnd_1790816 < baseStart_1790816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790823 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1790823 : Nat := 118140960795 + 1790823 * 2 ^ 59
def prefixEnd_1790823 : Nat := 4983230072969 + 3 ^ 40 * 1790823 * 2
def baseEnd_1790823 : Nat := 919552966126752130476661

theorem tailTrace_1790823 : CollatzResearch.WordTrace tailWord_1790823 prefixEnd_1790823 919552966126752130476661 := by
  unfold tailWord_1790823
  simp only [CollatzResearch.WordTrace]
  refine ⟨65316680791161594063689123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43544453860774396042459415 65316680791161594063689123)
  ·
    refine ⟨97975021186742391095533685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65316680791161594063689123 97975021186742391095533685)
    ·
      refine ⟨9185158236257099165206283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97975021186742391095533685 9185158236257099165206283)
      ·
        refine ⟨13777737354385648747809425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9185158236257099165206283 13777737354385648747809425)
        ·
          refine ⟨10333303015789236560857069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777737354385648747809425 10333303015789236560857069)
          ·
            refine ⟨3874988630920963710321401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10333303015789236560857069 3874988630920963710321401)
            ·
              refine ⟨2906241473190722782741051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874988630920963710321401 2906241473190722782741051)
              ·
                refine ⟨4359362209786084174111577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906241473190722782741051 4359362209786084174111577)
                ·
                  refine ⟨3269521657339563130583683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359362209786084174111577 3269521657339563130583683)
                  ·
                    refine ⟨4904282486009344695875525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269521657339563130583683 4904282486009344695875525)
                    ·
                      refine ⟨919552966126752130476661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904282486009344695875525 919552966126752130476661)
                      ·
                        rfl

theorem cell23_1790823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1790823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790823 prefixEnd_1790823 := by exact prefixLift 1790823
  have htrace : WordTrace (prefixWord ++ tailWord_1790823) baseStart_1790823 baseEnd_1790823 := by
    simpa [prefixWord, tailWord_1790823, baseEnd_1790823] using wordTrace_append hprefix tailTrace_1790823
  have hstable : (prefixWord ++ tailWord_1790823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790823).length < 2 ^ (prefixWord ++ tailWord_1790823).sum := by decide
  have hdescent : baseEnd_1790823 < baseStart_1790823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790923 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 6]
def baseStart_1790923 : Nat := 118140960795 + 1790923 * 2 ^ 59
def prefixEnd_1790923 : Nat := 4983230072969 + 3 ^ 40 * 1790923 * 2
def baseEnd_1790923 : Nat := 306534771397400579742067

theorem tailTrace_1790923 : CollatzResearch.WordTrace tailWord_1790923 prefixEnd_1790923 306534771397400579742067 := by
  unfold tailWord_1790923
  simp only [CollatzResearch.WordTrace]
  refine ⟨65320328090799311142329423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43546885393866207428219615 65320328090799311142329423)
  ·
    refine ⟨97980492136198966713494135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65320328090799311142329423 97980492136198966713494135)
    ·
      refine ⟨146970738204298450070241203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97980492136198966713494135 146970738204298450070241203)
      ·
        refine ⟨220456107306447675105361805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146970738204298450070241203 220456107306447675105361805)
        ·
          refine ⟨82671040239917878164510677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220456107306447675105361805 82671040239917878164510677)
          ·
            refine ⟨1937602505623075269480719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82671040239917878164510677 1937602505623075269480719)
            ·
              refine ⟨2906403758434612904221079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937602505623075269480719 2906403758434612904221079)
              ·
                refine ⟨4359605637651919356331619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906403758434612904221079 4359605637651919356331619)
                ·
                  refine ⟨6539408456477879034497429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359605637651919356331619 6539408456477879034497429)
                  ·
                    refine ⟨306534771397400579742067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6539408456477879034497429 306534771397400579742067)
                    ·
                      rfl

theorem cell23_1790923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 6].length) (baseStart_1790923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790923 prefixEnd_1790923 := by exact prefixLift 1790923
  have htrace : WordTrace (prefixWord ++ tailWord_1790923) baseStart_1790923 baseEnd_1790923 := by
    simpa [prefixWord, tailWord_1790923, baseEnd_1790923] using wordTrace_append hprefix tailTrace_1790923
  have hstable : (prefixWord ++ tailWord_1790923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790923).length < 2 ^ (prefixWord ++ tailWord_1790923).sum := by decide
  have hdescent : baseEnd_1790923 < baseStart_1790923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790930 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1790930 : Nat := 118140960795 + 1790930 * 2 ^ 59
def prefixEnd_1790930 : Nat := 4983230072969 + 3 ^ 40 * 1790930 * 2
def baseEnd_1790930 : Nat := 919607908556783211838669

theorem tailTrace_1790930 : CollatzResearch.WordTrace tailWord_1790930 prefixEnd_1790930 919607908556783211838669 := by
  unfold tailWord_1790930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330145850443487834458561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43547055601182634225222829 16330145850443487834458561)
  ·
    refine ⟨12247609387832615875843921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16330145850443487834458561 12247609387832615875843921)
    ·
      refine ⟨9185707040874461906882941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12247609387832615875843921 9185707040874461906882941)
      ·
        refine ⟨3444640140327923215081103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9185707040874461906882941 3444640140327923215081103)
        ·
          refine ⟨5166960210491884822621655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444640140327923215081103 5166960210491884822621655)
          ·
            refine ⟨7750440315737827233932483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166960210491884822621655 7750440315737827233932483)
            ·
              refine ⟨11625660473606740850898725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750440315737827233932483 11625660473606740850898725)
              ·
                refine ⟨2179811338801263909543511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11625660473606740850898725 2179811338801263909543511)
                ·
                  refine ⟨3269717008201895864315267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179811338801263909543511 3269717008201895864315267)
                  ·
                    refine ⟨4904575512302843796472901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269717008201895864315267 4904575512302843796472901)
                    ·
                      refine ⟨919607908556783211838669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904575512302843796472901 919607908556783211838669)
                      ·
                        rfl

theorem cell23_1790930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1790930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790930 prefixEnd_1790930 := by exact prefixLift 1790930
  have htrace : WordTrace (prefixWord ++ tailWord_1790930) baseStart_1790930 baseEnd_1790930 := by
    simpa [prefixWord, tailWord_1790930, baseEnd_1790930] using wordTrace_append hprefix tailTrace_1790930
  have hstable : (prefixWord ++ tailWord_1790930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790930).length < 2 ^ (prefixWord ++ tailWord_1790930).sum := by decide
  have hdescent : baseEnd_1790930 < baseStart_1790930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790936 : List Nat := [2, 1, 2, 2, 2, 4, 1, 9]
def baseStart_1790936 : Nat := 118140960795 + 1790936 * 2 ^ 59
def prefixEnd_1790936 : Nat := 4983230072969 + 3 ^ 40 * 1790936 * 2
def baseEnd_1790936 : Nat := 34059666275581858828283

theorem tailTrace_1790936 : CollatzResearch.WordTrace tailWord_1790936 prefixEnd_1790936 34059666275581858828283 := by
  unfold tailWord_1790936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660401119876107181276331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43547201493168142908368441 32660401119876107181276331)
  ·
    refine ⟨48990601679814160771914497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32660401119876107181276331 48990601679814160771914497)
    ·
      refine ⟨36742951259860620578935873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48990601679814160771914497 36742951259860620578935873)
      ·
        refine ⟨27557213444895465434201905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36742951259860620578935873 27557213444895465434201905)
        ·
          refine ⟨20667910083671599075651429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27557213444895465434201905 20667910083671599075651429)
          ·
            refine ⟨3875233140688424826684643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20667910083671599075651429 3875233140688424826684643)
            ·
              refine ⟨5812849711032637240026965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875233140688424826684643 5812849711032637240026965)
              ·
                refine ⟨34059666275581858828283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5812849711032637240026965 34059666275581858828283)
                ·
                  rfl

theorem cell23_1790936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 9].length) (baseStart_1790936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790936 prefixEnd_1790936 := by exact prefixLift 1790936
  have htrace : WordTrace (prefixWord ++ tailWord_1790936) baseStart_1790936 baseEnd_1790936 := by
    simpa [prefixWord, tailWord_1790936, baseEnd_1790936] using wordTrace_append hprefix tailTrace_1790936
  have hstable : (prefixWord ++ tailWord_1790936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790936).length < 2 ^ (prefixWord ++ tailWord_1790936).sum := by decide
  have hdescent : baseEnd_1790936 < baseStart_1790936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790973 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_1790973 : Nat := 118140960795 + 1790973 * 2 ^ 59
def prefixEnd_1790973 : Nat := 4983230072969 + 3 ^ 40 * 1790973 * 2
def baseEnd_1790973 : Nat := 919629988224926543600971

theorem tailTrace_1790973 : CollatzResearch.WordTrace tailWord_1790973 prefixEnd_1790973 919629988224926543600971 := by
  unfold tailWord_1790973
  simp only [CollatzResearch.WordTrace]
  refine ⟨65322151740618169681649573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43548101160412113121099715 65322151740618169681649573)
  ·
    refine ⟨12247903451365906815309295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65322151740618169681649573 12247903451365906815309295)
    ·
      refine ⟨18371855177048860222963943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247903451365906815309295 18371855177048860222963943)
      ·
        refine ⟨27557782765573290334445915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18371855177048860222963943 27557782765573290334445915)
        ·
          refine ⟨41336674148359935501668873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27557782765573290334445915 41336674148359935501668873)
          ·
            refine ⟨31002505611269951626251655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41336674148359935501668873 31002505611269951626251655)
            ·
              refine ⟨46503758416904927439377483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31002505611269951626251655 46503758416904927439377483)
              ·
                refine ⟨69755637625357391159066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46503758416904927439377483 69755637625357391159066225)
                ·
                  refine ⟨52316728219018043369299669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69755637625357391159066225 52316728219018043369299669)
                  ·
                    refine ⟨1226173317633235391467961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52316728219018043369299669 1226173317633235391467961)
                    ·
                      refine ⟨919629988224926543600971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1226173317633235391467961 919629988224926543600971)
                      ·
                        rfl

theorem cell23_1790973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_1790973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790973 prefixEnd_1790973 := by exact prefixLift 1790973
  have htrace : WordTrace (prefixWord ++ tailWord_1790973) baseStart_1790973 baseEnd_1790973 := by
    simpa [prefixWord, tailWord_1790973, baseEnd_1790973] using wordTrace_append hprefix tailTrace_1790973
  have hstable : (prefixWord ++ tailWord_1790973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790973).length < 2 ^ (prefixWord ++ tailWord_1790973).sum := by decide
  have hdescent : baseEnd_1790973 < baseStart_1790973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790994 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1790994 : Nat := 118140960795 + 1790994 * 2 ^ 59
def prefixEnd_1790994 : Nat := 4983230072969 + 3 ^ 40 * 1790994 * 2
def baseEnd_1790994 : Nat := 919640771318670961438375

theorem tailTrace_1790994 : CollatzResearch.WordTrace tailWord_1790994 prefixEnd_1790994 919640771318670961438375 := by
  unfold tailWord_1790994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330729418385522567041009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43548611782361393512109357 16330729418385522567041009)
  ·
    refine ⟨12248047063789141925280757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16330729418385522567041009 12248047063789141925280757)
    ·
      refine ⟨1148254412230232055495071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12248047063789141925280757 1148254412230232055495071)
      ·
        refine ⟨1722381618345348083242607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148254412230232055495071 1722381618345348083242607)
        ·
          refine ⟨2583572427518022124863911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722381618345348083242607 2583572427518022124863911)
          ·
            refine ⟨3875358641277033187295867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583572427518022124863911 3875358641277033187295867)
            ·
              refine ⟨5813037961915549780943801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875358641277033187295867 5813037961915549780943801)
              ·
                refine ⟨4359778471436662335707851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813037961915549780943801 4359778471436662335707851)
                ·
                  refine ⟨6539667707154993503561777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359778471436662335707851 6539667707154993503561777)
                  ·
                    refine ⟨4904750780366245127671333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6539667707154993503561777 4904750780366245127671333)
                    ·
                      refine ⟨919640771318670961438375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904750780366245127671333 919640771318670961438375)
                      ·
                        rfl

theorem cell23_1790994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1790994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1790994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1790994 prefixEnd_1790994 := by exact prefixLift 1790994
  have htrace : WordTrace (prefixWord ++ tailWord_1790994) baseStart_1790994 baseEnd_1790994 := by
    simpa [prefixWord, tailWord_1790994, baseEnd_1790994] using wordTrace_append hprefix tailTrace_1790994
  have hstable : (prefixWord ++ tailWord_1790994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790994).length < 2 ^ (prefixWord ++ tailWord_1790994).sum := by decide
  have hdescent : baseEnd_1790994 < baseStart_1790994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791030 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1791030 : Nat := 118140960795 + 1791030 * 2 ^ 59
def prefixEnd_1791030 : Nat := 4983230072969 + 3 ^ 40 * 1791030 * 2
def baseEnd_1791030 : Nat := 306553085540744273529403

theorem tailTrace_1791030 : CollatzResearch.WordTrace tailWord_1791030 prefixEnd_1791030 306553085540744273529403 := by
  unfold tailWord_1791030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082764418838229276029659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43549487134274445610983029 4082764418838229276029659)
  ·
    refine ⟨6124146628257343914044489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082764418838229276029659 6124146628257343914044489)
    ·
      refine ⟨4593109971193007935533367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6124146628257343914044489 4593109971193007935533367)
      ·
        refine ⟨6889664956789511903300051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593109971193007935533367 6889664956789511903300051)
        ·
          refine ⟨10334497435184267854950077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6889664956789511903300051 10334497435184267854950077)
          ·
            refine ⟨3875436538194100445606279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10334497435184267854950077 3875436538194100445606279)
            ·
              refine ⟨5813154807291150668409419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875436538194100445606279 5813154807291150668409419)
              ·
                refine ⟨8719732210936726002614129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813154807291150668409419 8719732210936726002614129)
                ·
                  refine ⟨6539799158202544501960597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719732210936726002614129 6539799158202544501960597)
                  ·
                    refine ⟨306553085540744273529403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6539799158202544501960597 306553085540744273529403)
                    ·
                      rfl

theorem cell23_1791030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1791030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791030 prefixEnd_1791030 := by exact prefixLift 1791030
  have htrace : WordTrace (prefixWord ++ tailWord_1791030) baseStart_1791030 baseEnd_1791030 := by
    simpa [prefixWord, tailWord_1791030, baseEnd_1791030] using wordTrace_append hprefix tailTrace_1791030
  have hstable : (prefixWord ++ tailWord_1791030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791030).length < 2 ^ (prefixWord ++ tailWord_1791030).sum := by decide
  have hdescent : baseEnd_1791030 < baseStart_1791030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791033 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1791033 : Nat := 118140960795 + 1791033 * 2 ^ 59
def prefixEnd_1791033 : Nat := 4983230072969 + 3 ^ 40 * 1791033 * 2
def baseEnd_1791033 : Nat := 919660797064196308850695

theorem tailTrace_1791033 : CollatzResearch.WordTrace tailWord_1791033 prefixEnd_1791033 919660797064196308850695 := by
  unfold tailWord_1791033
  simp only [CollatzResearch.WordTrace]
  refine ⟨65324340120400799928833753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43549560080267199952555835 65324340120400799928833753)
  ·
    refine ⟨48993255090300599946625315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65324340120400799928833753 48993255090300599946625315)
    ·
      refine ⟨73489882635450899919937973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48993255090300599946625315 73489882635450899919937973)
      ·
        refine ⟨6889676497073521867494185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73489882635450899919937973 6889676497073521867494185)
        ·
          refine ⟨5167257372805141400620639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889676497073521867494185 5167257372805141400620639)
          ·
            refine ⟨7750886059207712100930959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167257372805141400620639 7750886059207712100930959)
            ·
              refine ⟨11626329088811568151396439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750886059207712100930959 11626329088811568151396439)
              ·
                refine ⟨17439493633217352227094659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626329088811568151396439 17439493633217352227094659)
                ·
                  refine ⟨26159240449826028340641989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17439493633217352227094659 26159240449826028340641989)
                  ·
                    refine ⟨4904857584342380313870373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26159240449826028340641989 4904857584342380313870373)
                    ·
                      refine ⟨919660797064196308850695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4904857584342380313870373 919660797064196308850695)
                      ·
                        rfl

theorem cell23_1791033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1791033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791033 prefixEnd_1791033 := by exact prefixLift 1791033
  have htrace : WordTrace (prefixWord ++ tailWord_1791033) baseStart_1791033 baseEnd_1791033 := by
    simpa [prefixWord, tailWord_1791033, baseEnd_1791033] using wordTrace_append hprefix tailTrace_1791033
  have hstable : (prefixWord ++ tailWord_1791033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791033).length < 2 ^ (prefixWord ++ tailWord_1791033).sum := by decide
  have hdescent : baseEnd_1791033 < baseStart_1791033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791037 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1791037 : Nat := 118140960795 + 1791037 * 2 ^ 59
def prefixEnd_1791037 : Nat := 4983230072969 + 3 ^ 40 * 1791037 * 2
def baseEnd_1791037 : Nat := 919662850986814293200677

theorem tailTrace_1791037 : CollatzResearch.WordTrace tailWord_1791037 prefixEnd_1791037 919662850986814293200677 := by
  unfold tailWord_1791037
  simp only [CollatzResearch.WordTrace]
  refine ⟨65324486012386308611979365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43549657341590872407986243 65324486012386308611979365)
  ·
    refine ⟨12248341127322432864746131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65324486012386308611979365 12248341127322432864746131)
    ·
      refine ⟨18372511690983649297119197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12248341127322432864746131 18372511690983649297119197)
      ·
        refine ⟨6889691884118868486419699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18372511690983649297119197 6889691884118868486419699)
        ·
          refine ⟨10334537826178302729629549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6889691884118868486419699 10334537826178302729629549)
          ·
            refine ⟨3875451684816863523611081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10334537826178302729629549 3875451684816863523611081)
            ·
              refine ⟨2906588763612647642708311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875451684816863523611081 2906588763612647642708311)
              ·
                refine ⟨4359883145418971464062467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906588763612647642708311 4359883145418971464062467)
                ·
                  refine ⟨6539824718128457196093701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359883145418971464062467 6539824718128457196093701)
                  ·
                    refine ⟨1226217134649085724267569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539824718128457196093701 1226217134649085724267569)
                    ·
                      refine ⟨919662850986814293200677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1226217134649085724267569 919662850986814293200677)
                      ·
                        rfl

theorem cell23_1791037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1791037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791037 prefixEnd_1791037 := by exact prefixLift 1791037
  have htrace : WordTrace (prefixWord ++ tailWord_1791037) baseStart_1791037 baseEnd_1791037 := by
    simpa [prefixWord, tailWord_1791037, baseEnd_1791037] using wordTrace_append hprefix tailTrace_1791037
  have hstable : (prefixWord ++ tailWord_1791037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791037).length < 2 ^ (prefixWord ++ tailWord_1791037).sum := by decide
  have hdescent : baseEnd_1791037 < baseStart_1791037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791060 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 5]
def baseStart_1791060 : Nat := 118140960795 + 1791060 * 2 ^ 59
def prefixEnd_1791060 : Nat := 4983230072969 + 3 ^ 40 * 1791060 * 2
def baseEnd_1791060 : Nat := 102186073449096411468119

theorem tailTrace_1791060 : CollatzResearch.WordTrace tailWord_1791060 prefixEnd_1791060 102186073449096411468119 := by
  unfold tailWord_1791060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662662445651491770033317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43550216594201989026711089 32662662445651491770033317)
  ·
    refine ⟨6124249208559654706881247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32662662445651491770033317 6124249208559654706881247)
    ·
      refine ⟨9186373812839482060321871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124249208559654706881247 9186373812839482060321871)
      ·
        refine ⟨13779560719259223090482807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186373812839482060321871 13779560719259223090482807)
        ·
          refine ⟨20669341078888834635724211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13779560719259223090482807 20669341078888834635724211)
          ·
            refine ⟨31004011618333251953586317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20669341078888834635724211 31004011618333251953586317)
            ·
              refine ⟨11626504356874969482594869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31004011618333251953586317 11626504356874969482594869)
              ·
                refine ⟨1089984783457028388993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11626504356874969482594869 1089984783457028388993269)
                ·
                  refine ⟨102186073449096411468119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089984783457028388993269 102186073449096411468119)
                  ·
                    rfl

theorem cell23_1791060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_1791060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791060 prefixEnd_1791060 := by exact prefixLift 1791060
  have htrace : WordTrace (prefixWord ++ tailWord_1791060) baseStart_1791060 baseEnd_1791060 := by
    simpa [prefixWord, tailWord_1791060, baseEnd_1791060] using wordTrace_append hprefix tailTrace_1791060
  have hstable : (prefixWord ++ tailWord_1791060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791060).length < 2 ^ (prefixWord ++ tailWord_1791060).sum := by decide
  have hdescent : baseEnd_1791060 < baseStart_1791060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791073 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1791073 : Nat := 118140960795 + 1791073 * 2 ^ 59
def prefixEnd_1791073 : Nat := 4983230072969 + 3 ^ 40 * 1791073 * 2
def baseEnd_1791073 : Nat := 306560445430125384116837

theorem tailTrace_1791073 : CollatzResearch.WordTrace tailWord_1791073 prefixEnd_1791073 306560445430125384116837 := by
  unfold tailWord_1791073
  simp only [CollatzResearch.WordTrace]
  refine ⟨65325799040255886760289873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43550532693503924506859915 65325799040255886760289873)
  ·
    refine ⟨48994349280191915070217405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65325799040255886760289873 48994349280191915070217405)
    ·
      refine ⟨18372880980071968151331527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48994349280191915070217405 18372880980071968151331527)
      ·
        refine ⟨27559321470107952226997291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18372880980071968151331527 27559321470107952226997291)
        ·
          refine ⟨41338982205161928340495937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559321470107952226997291 41338982205161928340495937)
          ·
            refine ⟨31004236653871446255371953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41338982205161928340495937 31004236653871446255371953)
            ·
              refine ⟨23253177490403584691528965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31004236653871446255371953 23253177490403584691528965)
              ·
                refine ⟨4359970779450672129661681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23253177490403584691528965 4359970779450672129661681)
                ·
                  refine ⟨3269978084588004097246261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359970779450672129661681 3269978084588004097246261)
                  ·
                    refine ⟨306560445430125384116837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3269978084588004097246261 306560445430125384116837)
                    ·
                      rfl

theorem cell23_1791073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1791073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791073 prefixEnd_1791073 := by exact prefixLift 1791073
  have htrace : WordTrace (prefixWord ++ tailWord_1791073) baseStart_1791073 baseEnd_1791073 := by
    simpa [prefixWord, tailWord_1791073, baseEnd_1791073] using wordTrace_append hprefix tailTrace_1791073
  have hstable : (prefixWord ++ tailWord_1791073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791073).length < 2 ^ (prefixWord ++ tailWord_1791073).sum := by decide
  have hdescent : baseEnd_1791073 < baseStart_1791073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791133 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 8]
def baseStart_1791133 : Nat := 118140960795 + 1791133 * 2 ^ 59
def prefixEnd_1791133 : Nat := 4983230072969 + 3 ^ 40 * 1791133 * 2
def baseEnd_1791133 : Nat := 102190238347738435288915

theorem tailTrace_1791133 : CollatzResearch.WordTrace tailWord_1791133 prefixEnd_1791133 102190238347738435288915 := by
  unfold tailWord_1791133
  simp only [CollatzResearch.WordTrace]
  refine ⟨65327987420038517007474053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43551991613359011338316035 65327987420038517007474053)
  ·
    refine ⟨12248997641257221938901385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65327987420038517007474053 12248997641257221938901385)
    ·
      refine ⟨9186748230942916454176039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12248997641257221938901385 9186748230942916454176039)
      ·
        refine ⟨13780122346414374681264059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186748230942916454176039 13780122346414374681264059)
        ·
          refine ⟨20670183519621562021896089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780122346414374681264059 20670183519621562021896089)
          ·
            refine ⟨15502637639716171516422067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20670183519621562021896089 15502637639716171516422067)
            ·
              refine ⟨23253956459574257274633101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15502637639716171516422067 23253956459574257274633101)
              ·
                refine ⟨8720233672340346477987413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23253956459574257274633101 8720233672340346477987413)
                ·
                  refine ⟨102190238347738435288915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8720233672340346477987413 102190238347738435288915)
                  ·
                    rfl

theorem cell23_1791133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_1791133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791133 prefixEnd_1791133 := by exact prefixLift 1791133
  have htrace : WordTrace (prefixWord ++ tailWord_1791133) baseStart_1791133 baseEnd_1791133 := by
    simpa [prefixWord, tailWord_1791133, baseEnd_1791133] using wordTrace_append hprefix tailTrace_1791133
  have hstable : (prefixWord ++ tailWord_1791133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791133).length < 2 ^ (prefixWord ++ tailWord_1791133).sum := by decide
  have hdescent : baseEnd_1791133 < baseStart_1791133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791193 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_1791193 : Nat := 118140960795 + 1791193 * 2 ^ 59
def prefixEnd_1791193 : Nat := 4983230072969 + 3 ^ 40 * 1791193 * 2
def baseEnd_1791193 : Nat := 306580984656305227616653

theorem tailTrace_1791193 : CollatzResearch.WordTrace tailWord_1791193 prefixEnd_1791193 306580984656305227616653 := by
  unfold tailWord_1791193
  simp only [CollatzResearch.WordTrace]
  refine ⟨65330175799821147254658233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43553450533214098169772155 65330175799821147254658233)
  ·
    refine ⟨48997631849865860440993675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65330175799821147254658233 48997631849865860440993675)
    ·
      refine ⟨73496447774798790661490513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997631849865860440993675 73496447774798790661490513)
      ·
        refine ⟨55122335831099092996117885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73496447774798790661490513 55122335831099092996117885)
        ·
          refine ⟨20670875936662159873544207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55122335831099092996117885 20670875936662159873544207)
          ·
            refine ⟨31006313904993239810316311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20670875936662159873544207 31006313904993239810316311)
            ·
              refine ⟨46509470857489859715474467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31006313904993239810316311 46509470857489859715474467)
              ·
                refine ⟨69764206286234789573211701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46509470857489859715474467 69764206286234789573211701)
                ·
                  refine ⟨6540394339334511522488597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69764206286234789573211701 6540394339334511522488597)
                  ·
                    refine ⟨306580984656305227616653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6540394339334511522488597 306580984656305227616653)
                    ·
                      rfl

theorem cell23_1791193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_1791193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791193 prefixEnd_1791193 := by exact prefixLift 1791193
  have htrace : WordTrace (prefixWord ++ tailWord_1791193) baseStart_1791193 baseEnd_1791193 := by
    simpa [prefixWord, tailWord_1791193, baseEnd_1791193] using wordTrace_append hprefix tailTrace_1791193
  have hstable : (prefixWord ++ tailWord_1791193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791193).length < 2 ^ (prefixWord ++ tailWord_1791193).sum := by decide
  have hdescent : baseEnd_1791193 < baseStart_1791193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791200 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1791200 : Nat := 118140960795 + 1791200 * 2 ^ 59
def prefixEnd_1791200 : Nat := 4983230072969 + 3 ^ 40 * 1791200 * 2
def baseEnd_1791200 : Nat := 919746548333497155462427

theorem tailTrace_1791200 : CollatzResearch.WordTrace tailWord_1791200 prefixEnd_1791200 919746548333497155462427 := by
  unfold tailWord_1791200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665215555397893725081527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43553620740530524966775369 32665215555397893725081527)
  ·
    refine ⟨48997823333096840587622291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665215555397893725081527 48997823333096840587622291)
    ·
      refine ⟨73496734999645260881433437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997823333096840587622291 73496734999645260881433437)
      ·
        refine ⟨27561275624866972830537539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73496734999645260881433437 27561275624866972830537539)
        ·
          refine ⟨41341913437300459245806309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27561275624866972830537539 41341913437300459245806309)
          ·
            refine ⟨7751608769493836108588683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41341913437300459245806309 7751608769493836108588683)
            ·
              refine ⟨11627413154240754162883025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751608769493836108588683 11627413154240754162883025)
              ·
                refine ⟨8720559865680565622162269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11627413154240754162883025 8720559865680565622162269)
                ·
                  refine ⟨3270209949630212108310851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8720559865680565622162269 3270209949630212108310851)
                  ·
                    refine ⟨4905314924445318162466277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270209949630212108310851 4905314924445318162466277)
                    ·
                      refine ⟨919746548333497155462427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4905314924445318162466277 919746548333497155462427)
                      ·
                        rfl

theorem cell23_1791200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1791200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791200 prefixEnd_1791200 := by exact prefixLift 1791200
  have htrace : WordTrace (prefixWord ++ tailWord_1791200) baseStart_1791200 baseEnd_1791200 := by
    simpa [prefixWord, tailWord_1791200, baseEnd_1791200] using wordTrace_append hprefix tailTrace_1791200
  have hstable : (prefixWord ++ tailWord_1791200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791200).length < 2 ^ (prefixWord ++ tailWord_1791200).sum := by decide
  have hdescent : baseEnd_1791200 < baseStart_1791200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791210 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1791210 : Nat := 118140960795 + 1791210 * 2 ^ 59
def prefixEnd_1791210 : Nat := 4983230072969 + 3 ^ 40 * 1791210 * 2
def baseEnd_1791210 : Nat := 306583894380014038779127

theorem tailTrace_1791210 : CollatzResearch.WordTrace tailWord_1791210 prefixEnd_1791210 306583894380014038779127 := by
  unfold tailWord_1791210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332698960189889789506771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43553863893839706105351389 16332698960189889789506771)
  ·
    refine ⟨24499048440284834684260157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16332698960189889789506771 24499048440284834684260157)
    ·
      refine ⟨9187143165106813006597559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24499048440284834684260157 9187143165106813006597559)
      ·
        refine ⟨13780714747660219509896339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9187143165106813006597559 13780714747660219509896339)
        ·
          refine ⟨20671072121490329264844509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780714747660219509896339 20671072121490329264844509)
          ·
            refine ⟨7751652045558873474316691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20671072121490329264844509 7751652045558873474316691)
            ·
              refine ⟨11627478068338310211475037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751652045558873474316691 11627478068338310211475037)
              ·
                refine ⟨4360304275626866329303139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11627478068338310211475037 4360304275626866329303139)
                ·
                  refine ⟨6540456413440299493954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360304275626866329303139 6540456413440299493954709)
                  ·
                    refine ⟨306583894380014038779127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6540456413440299493954709 306583894380014038779127)
                    ·
                      rfl

theorem cell23_1791210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1791210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791210 prefixEnd_1791210 := by exact prefixLift 1791210
  have htrace : WordTrace (prefixWord ++ tailWord_1791210) baseStart_1791210 baseEnd_1791210 := by
    simpa [prefixWord, tailWord_1791210, baseEnd_1791210] using wordTrace_append hprefix tailTrace_1791210
  have hstable : (prefixWord ++ tailWord_1791210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791210).length < 2 ^ (prefixWord ++ tailWord_1791210).sum := by decide
  have hdescent : baseEnd_1791210 < baseStart_1791210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791237 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_1791237 : Nat := 118140960795 + 1791237 * 2 ^ 59
def prefixEnd_1791237 : Nat := 4983230072969 + 3 ^ 40 * 1791237 * 2
def baseEnd_1791237 : Nat := 919765547117713510699757

theorem tailTrace_1791237 : CollatzResearch.WordTrace tailWord_1791237 prefixEnd_1791237 919765547117713510699757 := by
  unfold tailWord_1791237
  simp only [CollatzResearch.WordTrace]
  refine ⟨65331780611661742769259965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43554520407774495179506643 65331780611661742769259965)
  ·
    refine ⟨24499417729373153538472487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65331780611661742769259965 24499417729373153538472487)
    ·
      refine ⟨36749126594059730307708731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24499417729373153538472487 36749126594059730307708731)
      ·
        refine ⟨55123689891089595461563097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36749126594059730307708731 55123689891089595461563097)
        ·
          refine ⟨41342767418317196596172323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55123689891089595461563097 41342767418317196596172323)
          ·
            refine ⟨62014151127475794894258485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41342767418317196596172323 62014151127475794894258485)
            ·
              refine ⟨5813826668200855771336733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62014151127475794894258485 5813826668200855771336733)
              ·
                refine ⟨2180185000575320914251275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813826668200855771336733 2180185000575320914251275)
                ·
                  refine ⟨3270277500862981371376913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180185000575320914251275 3270277500862981371376913)
                  ·
                    refine ⟨2452708125647236028532685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270277500862981371376913 2452708125647236028532685)
                    ·
                      refine ⟨919765547117713510699757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2452708125647236028532685 919765547117713510699757)
                      ·
                        rfl

theorem cell23_1791237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_1791237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791237 prefixEnd_1791237 := by exact prefixLift 1791237
  have htrace : WordTrace (prefixWord ++ tailWord_1791237) baseStart_1791237 baseEnd_1791237 := by
    simpa [prefixWord, tailWord_1791237, baseEnd_1791237] using wordTrace_append hprefix tailTrace_1791237
  have hstable : (prefixWord ++ tailWord_1791237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791237).length < 2 ^ (prefixWord ++ tailWord_1791237).sum := by decide
  have hdescent : baseEnd_1791237 < baseStart_1791237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791240 : List Nat := [2, 1, 3, 2, 4, 1, 10]
def baseStart_1791240 : Nat := 118140960795 + 1791240 * 2 ^ 59
def prefixEnd_1791240 : Nat := 4983230072969 + 3 ^ 40 * 1791240 * 2
def baseEnd_1791240 : Nat := 11355149229131814802003

theorem tailTrace_1791240 : CollatzResearch.WordTrace tailWord_1791240 prefixEnd_1791240 11355149229131814802003 := by
  unfold tailWord_1791240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665945015325437140809587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43554593353767249521079449 32665945015325437140809587)
  ·
    refine ⟨48998917522988155711214381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665945015325437140809587 48998917522988155711214381)
    ·
      refine ⟨18374594071120558391705393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48998917522988155711214381 18374594071120558391705393)
      ·
        refine ⟨13780945553340418793779045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18374594071120558391705393 13780945553340418793779045)
        ·
          refine ⟨2583927291251328523833571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13780945553340418793779045 2583927291251328523833571)
          ·
            refine ⟨3875890936876992785750357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583927291251328523833571 3875890936876992785750357)
            ·
              refine ⟨11355149229131814802003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3875890936876992785750357 11355149229131814802003)
              ·
                rfl

theorem cell23_1791240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 10].length) (baseStart_1791240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791240 prefixEnd_1791240 := by exact prefixLift 1791240
  have htrace : WordTrace (prefixWord ++ tailWord_1791240) baseStart_1791240 baseEnd_1791240 := by
    simpa [prefixWord, tailWord_1791240, baseEnd_1791240] using wordTrace_append hprefix tailTrace_1791240
  have hstable : (prefixWord ++ tailWord_1791240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791240).length < 2 ^ (prefixWord ++ tailWord_1791240).sum := by decide
  have hdescent : baseEnd_1791240 < baseStart_1791240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791244 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_1791244 : Nat := 118140960795 + 1791244 * 2 ^ 59
def prefixEnd_1791244 : Nat := 4983230072969 + 3 ^ 40 * 1791244 * 2
def baseEnd_1791244 : Nat := 306589713827431661104075

theorem tailTrace_1791244 : CollatzResearch.WordTrace tailWord_1791244 prefixEnd_1791244 306589713827431661104075 := by
  unfold tailWord_1791244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666017961318191482382393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43554690615090921976509857 32666017961318191482382393)
  ·
    refine ⟨24499513470988643611786795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32666017961318191482382393 24499513470988643611786795)
    ·
      refine ⟨36749270206482965417680193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24499513470988643611786795 36749270206482965417680193)
      ·
        refine ⟨27561952654862224063260145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36749270206482965417680193 27561952654862224063260145)
        ·
          refine ⟨20671464491146668047445109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27561952654862224063260145 20671464491146668047445109)
          ·
            refine ⟨1937949796045000129447979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20671464491146668047445109 1937949796045000129447979)
            ·
              refine ⟨2906924694067500194171969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937949796045000129447979 2906924694067500194171969)
              ·
                refine ⟨2180193520550625145628977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906924694067500194171969 2180193520550625145628977)
                ·
                  refine ⟨1635145140412968859221733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180193520550625145628977 1635145140412968859221733)
                  ·
                    refine ⟨306589713827431661104075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635145140412968859221733 306589713827431661104075)
                    ·
                      rfl

theorem cell23_1791244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_1791244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791244 prefixEnd_1791244 := by exact prefixLift 1791244
  have htrace : WordTrace (prefixWord ++ tailWord_1791244) baseStart_1791244 baseEnd_1791244 := by
    simpa [prefixWord, tailWord_1791244, baseEnd_1791244] using wordTrace_append hprefix tailTrace_1791244
  have hstable : (prefixWord ++ tailWord_1791244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791244).length < 2 ^ (prefixWord ++ tailWord_1791244).sum := by decide
  have hdescent : baseEnd_1791244 < baseStart_1791244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791261 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1791261 : Nat := 118140960795 + 1791261 * 2 ^ 59
def prefixEnd_1791261 : Nat := 4983230072969 + 3 ^ 40 * 1791261 * 2
def baseEnd_1791261 : Nat := 306592623551140472266549

theorem tailTrace_1791261 : CollatzResearch.WordTrace tailWord_1791261 prefixEnd_1791261 306592623551140472266549 := by
  unfold tailWord_1791261
  simp only [CollatzResearch.WordTrace]
  refine ⟨65332655963574794868133637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43555103975716529912089091 65332655963574794868133637)
  ·
    refine ⟨12249872993170274037775057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65332655963574794868133637 12249872993170274037775057)
    ·
      refine ⟨9187404744877705528331293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12249872993170274037775057 9187404744877705528331293)
      ·
        refine ⟨3445276779329139573124235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9187404744877705528331293 3445276779329139573124235)
        ·
          refine ⟨5167915168993709359686353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445276779329139573124235 5167915168993709359686353)
          ·
            refine ⟨3875936376745282019764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167915168993709359686353 3875936376745282019764765)
            ·
              refine ⟨1453476141279480757411787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3875936376745282019764765 1453476141279480757411787)
              ·
                refine ⟨2180214211919221136117681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453476141279480757411787 2180214211919221136117681)
                ·
                  refine ⟨1635160658939415852088261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180214211919221136117681 1635160658939415852088261)
                  ·
                    refine ⟨306592623551140472266549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635160658939415852088261 306592623551140472266549)
                    ·
                      rfl

theorem cell23_1791261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1791261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791261 prefixEnd_1791261 := by exact prefixLift 1791261
  have htrace : WordTrace (prefixWord ++ tailWord_1791261) baseStart_1791261 baseEnd_1791261 := by
    simpa [prefixWord, tailWord_1791261, baseEnd_1791261] using wordTrace_append hprefix tailTrace_1791261
  have hstable : (prefixWord ++ tailWord_1791261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791261).length < 2 ^ (prefixWord ++ tailWord_1791261).sum := by decide
  have hdescent : baseEnd_1791261 < baseStart_1791261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791264 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1791264 : Nat := 118140960795 + 1791264 * 2 ^ 59
def prefixEnd_1791264 : Nat := 4983230072969 + 3 ^ 40 * 1791264 * 2
def baseEnd_1791264 : Nat := 919779411095384905062133

theorem tailTrace_1791264 : CollatzResearch.WordTrace tailWord_1791264 prefixEnd_1791264 919779411095384905062133 := by
  unfold tailWord_1791264
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666382691281963190246423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43555176921709284253661897 32666382691281963190246423)
  ·
    refine ⟨48999574036922944785369635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32666382691281963190246423 48999574036922944785369635)
    ·
      refine ⟨73499361055384417178054453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48999574036922944785369635 73499361055384417178054453)
      ·
        refine ⟨6890565098942289110442605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73499361055384417178054453 6890565098942289110442605)
        ·
          refine ⟨2583961912103358416415977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6890565098942289110442605 2583961912103358416415977)
          ·
            refine ⟨1937971434077518812311983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583961912103358416415977 1937971434077518812311983)
            ·
              refine ⟨2906957151116278218467975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937971434077518812311983 2906957151116278218467975)
              ·
                refine ⟨4360435726674417327701963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906957151116278218467975 4360435726674417327701963)
                ·
                  refine ⟨6540653590011625991552945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360435726674417327701963 6540653590011625991552945)
                  ·
                    refine ⟨4905490192508719493664709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540653590011625991552945 4905490192508719493664709)
                    ·
                      refine ⟨919779411095384905062133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4905490192508719493664709 919779411095384905062133)
                      ·
                        rfl

theorem cell23_1791264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1791264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791264 prefixEnd_1791264 := by exact prefixLift 1791264
  have htrace : WordTrace (prefixWord ++ tailWord_1791264) baseStart_1791264 baseEnd_1791264 := by
    simpa [prefixWord, tailWord_1791264, baseEnd_1791264] using wordTrace_append hprefix tailTrace_1791264
  have hstable : (prefixWord ++ tailWord_1791264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791264).length < 2 ^ (prefixWord ++ tailWord_1791264).sum := by decide
  have hdescent : baseEnd_1791264 < baseStart_1791264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791267 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1791267 : Nat := 118140960795 + 1791267 * 2 ^ 59
def prefixEnd_1791267 : Nat := 4983230072969 + 3 ^ 40 * 1791267 * 2
def baseEnd_1791267 : Nat := 919780951537348393324619

theorem tailTrace_1791267 : CollatzResearch.WordTrace tailWord_1791267 prefixEnd_1791267 919780951537348393324619 := by
  unfold tailWord_1791267
  simp only [CollatzResearch.WordTrace]
  refine ⟨65332874801553057892852055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43555249867702038595234703 65332874801553057892852055)
  ·
    refine ⟨97999312202329586839278083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65332874801553057892852055 97999312202329586839278083)
    ·
      refine ⟨146998968303494380258917125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97999312202329586839278083 146998968303494380258917125)
      ·
        refine ⟨27562306556905196298546961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146998968303494380258917125 27562306556905196298546961)
        ·
          refine ⟨20671729917678897223910221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27562306556905196298546961 20671729917678897223910221)
          ·
            refine ⟨7751898719129586458966333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20671729917678897223910221 7751898719129586458966333)
            ·
              refine ⟨2906962019673594922112375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7751898719129586458966333 2906962019673594922112375)
              ·
                refine ⟨4360443029510392383168563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906962019673594922112375 4360443029510392383168563)
                ·
                  refine ⟨6540664544265588574752845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360443029510392383168563 6540664544265588574752845)
                  ·
                    refine ⟨2452749204099595715532317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6540664544265588574752845 2452749204099595715532317)
                    ·
                      refine ⟨919780951537348393324619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2452749204099595715532317 919780951537348393324619)
                      ·
                        rfl

theorem cell23_1791267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1791267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791267 prefixEnd_1791267 := by exact prefixLift 1791267
  have htrace : WordTrace (prefixWord ++ tailWord_1791267) baseStart_1791267 baseEnd_1791267 := by
    simpa [prefixWord, tailWord_1791267, baseEnd_1791267] using wordTrace_append hprefix tailTrace_1791267
  have hstable : (prefixWord ++ tailWord_1791267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791267).length < 2 ^ (prefixWord ++ tailWord_1791267).sum := by decide
  have hdescent : baseEnd_1791267 < baseStart_1791267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791274 : List Nat := [3, 1, 4, 2, 1, 3, 2, 7]
def baseStart_1791274 : Nat := 118140960795 + 1791274 * 2 ^ 59
def prefixEnd_1791274 : Nat := 4983230072969 + 3 ^ 40 * 1791274 * 2
def baseEnd_1791274 : Nat := 34066094292664069108781

theorem tailTrace_1791274 : CollatzResearch.WordTrace tailWord_1791274 prefixEnd_1791274 34066094292664069108781 := by
  unfold tailWord_1791274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333282528131924522089219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43555420075018465392237917 16333282528131924522089219)
  ·
    refine ⟨24499923792197886783133829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16333282528131924522089219 24499923792197886783133829)
    ·
      refine ⟨4593735711037103771837593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24499923792197886783133829 4593735711037103771837593)
      ·
        refine ⟨3445301783277827828878195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4593735711037103771837593 3445301783277827828878195)
        ·
          refine ⟨5167952674916741743317293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445301783277827828878195 5167952674916741743317293)
          ·
            refine ⟨1937982253093778153743985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5167952674916741743317293 1937982253093778153743985)
            ·
              refine ⟨1453486689820333615307989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937982253093778153743985 1453486689820333615307989)
              ·
                refine ⟨34066094292664069108781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1453486689820333615307989 34066094292664069108781)
                ·
                  rfl

theorem cell23_1791274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_1791274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791274 prefixEnd_1791274 := by exact prefixLift 1791274
  have htrace : WordTrace (prefixWord ++ tailWord_1791274) baseStart_1791274 baseEnd_1791274 := by
    simpa [prefixWord, tailWord_1791274, baseEnd_1791274] using wordTrace_append hprefix tailTrace_1791274
  have hstable : (prefixWord ++ tailWord_1791274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791274).length < 2 ^ (prefixWord ++ tailWord_1791274).sum := by decide
  have hdescent : baseEnd_1791274 < baseStart_1791274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791284 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1791284 : Nat := 118140960795 + 1791284 * 2 ^ 59
def prefixEnd_1791284 : Nat := 4983230072969 + 3 ^ 40 * 1791284 * 2
def baseEnd_1791284 : Nat := 919789680708474826812041

theorem tailTrace_1791284 : CollatzResearch.WordTrace tailWord_1791284 prefixEnd_1791284 919789680708474826812041 := by
  unfold tailWord_1791284
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666747421245734898110453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43555663228327646530813937 32666747421245734898110453)
  ·
    refine ⟨3062507570741787646697855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32666747421245734898110453 3062507570741787646697855)
    ·
      refine ⟨4593761356112681470046783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062507570741787646697855 4593761356112681470046783)
      ·
        refine ⟨6890642034169022205070175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593761356112681470046783 6890642034169022205070175)
        ·
          refine ⟨10335963051253533307605263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890642034169022205070175 10335963051253533307605263)
          ·
            refine ⟨15503944576880299961407895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10335963051253533307605263 15503944576880299961407895)
            ·
              refine ⟨23255916865320449942111843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15503944576880299961407895 23255916865320449942111843)
              ·
                refine ⟨34883875297980674913167765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23255916865320449942111843 34883875297980674913167765)
                ·
                  refine ⟨1635181654592844136554739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34883875297980674913167765 1635181654592844136554739)
                  ·
                    refine ⟨2452772481889266204832109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635181654592844136554739 2452772481889266204832109)
                    ·
                      refine ⟨919789680708474826812041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2452772481889266204832109 919789680708474826812041)
                      ·
                        rfl

theorem cell23_1791284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1791284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791284 prefixEnd_1791284 := by exact prefixLift 1791284
  have htrace : WordTrace (prefixWord ++ tailWord_1791284) baseStart_1791284 baseEnd_1791284 := by
    simpa [prefixWord, tailWord_1791284, baseEnd_1791284] using wordTrace_append hprefix tailTrace_1791284
  have hstable : (prefixWord ++ tailWord_1791284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791284).length < 2 ^ (prefixWord ++ tailWord_1791284).sum := by decide
  have hdescent : baseEnd_1791284 < baseStart_1791284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791302 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1791302 : Nat := 118140960795 + 1791302 * 2 ^ 59
def prefixEnd_1791302 : Nat := 4983230072969 + 3 ^ 40 * 1791302 * 2
def baseEnd_1791302 : Nat := 919798923360255756386959

theorem tailTrace_1791302 : CollatzResearch.WordTrace tailWord_1791302 prefixEnd_1791302 919798923360255756386959 := by
  unfold tailWord_1791302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041692229888320589699255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43556100904284172580250773 2041692229888320589699255)
  ·
    refine ⟨3062538344832480884548883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041692229888320589699255 3062538344832480884548883)
    ·
      refine ⟨4593807517248721326823325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062538344832480884548883 4593807517248721326823325)
      ·
        refine ⟨1722677818968270497558747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4593807517248721326823325 1722677818968270497558747)
        ·
          refine ⟨2584016728452405746338121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722677818968270497558747 2584016728452405746338121)
          ·
            refine ⟨1938012546339304309753591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584016728452405746338121 1938012546339304309753591)
            ·
              refine ⟨2907018819508956464630387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938012546339304309753591 2907018819508956464630387)
              ·
                refine ⟨4360528229263434696945581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907018819508956464630387 4360528229263434696945581)
                ·
                  refine ⟨1635198085973788011354593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4360528229263434696945581 1635198085973788011354593)
                  ·
                    refine ⟨1226398564480341008515945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1635198085973788011354593 1226398564480341008515945)
                    ·
                      refine ⟨919798923360255756386959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1226398564480341008515945 919798923360255756386959)
                      ·
                        rfl

theorem cell23_1791302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1791302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791302 prefixEnd_1791302 := by exact prefixLift 1791302
  have htrace : WordTrace (prefixWord ++ tailWord_1791302) baseStart_1791302 baseEnd_1791302 := by
    simpa [prefixWord, tailWord_1791302, baseEnd_1791302] using wordTrace_append hprefix tailTrace_1791302
  have hstable : (prefixWord ++ tailWord_1791302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791302).length < 2 ^ (prefixWord ++ tailWord_1791302).sum := by decide
  have hdescent : baseEnd_1791302 < baseStart_1791302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791310 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1791310 : Nat := 118140960795 + 1791310 * 2 ^ 59
def prefixEnd_1791310 : Nat := 4983230072969 + 3 ^ 40 * 1791310 * 2
def baseEnd_1791310 : Nat := 919803031205491725086921

theorem tailTrace_1791310 : CollatzResearch.WordTrace tailWord_1791310 prefixEnd_1791310 919803031205491725086921 := by
  unfold tailWord_1791310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166805392549659529583423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43556295426931517491111589 8166805392549659529583423)
  ·
    refine ⟨12250208088824489294375135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8166805392549659529583423 12250208088824489294375135)
    ·
      refine ⟨18375312133236733941562703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250208088824489294375135 18375312133236733941562703)
      ·
        refine ⟨27562968199855100912344055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375312133236733941562703 27562968199855100912344055)
        ·
          refine ⟨41344452299782651368516083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27562968199855100912344055 41344452299782651368516083)
          ·
            refine ⟨62016678449673977052774125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41344452299782651368516083 62016678449673977052774125)
            ·
              refine ⟨23256254418627741394790297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62016678449673977052774125 23256254418627741394790297)
              ·
                refine ⟨17442190813970806046092723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23256254418627741394790297 17442190813970806046092723)
                ·
                  refine ⟨26163286220956209069139085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17442190813970806046092723 26163286220956209069139085)
                  ·
                    refine ⟨9811232332858578400927157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26163286220956209069139085 9811232332858578400927157)
                    ·
                      refine ⟨919803031205491725086921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9811232332858578400927157 919803031205491725086921)
                      ·
                        rfl

theorem cell23_1791310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1791310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791310 prefixEnd_1791310 := by exact prefixLift 1791310
  have htrace : WordTrace (prefixWord ++ tailWord_1791310) baseStart_1791310 baseEnd_1791310 := by
    simpa [prefixWord, tailWord_1791310, baseEnd_1791310] using wordTrace_append hprefix tailTrace_1791310
  have hstable : (prefixWord ++ tailWord_1791310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791310).length < 2 ^ (prefixWord ++ tailWord_1791310).sum := by decide
  have hdescent : baseEnd_1791310 < baseStart_1791310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791320 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1791320 : Nat := 118140960795 + 1791320 * 2 ^ 59
def prefixEnd_1791320 : Nat := 4983230072969 + 3 ^ 40 * 1791320 * 2
def baseEnd_1791320 : Nat := 919808166012036685961875

theorem tailTrace_1791320 : CollatzResearch.WordTrace tailWord_1791320 prefixEnd_1791320 919808166012036685961875 := by
  unfold tailWord_1791320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32667403935180523972265707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43556538580240698629687609 32667403935180523972265707)
  ·
    refine ⟨49001105902770785958398561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32667403935180523972265707 49001105902770785958398561)
    ·
      refine ⟨36750829427078089468798921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49001105902770785958398561 36750829427078089468798921)
      ·
        refine ⟨27563122070308567101599191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36750829427078089468798921 27563122070308567101599191)
        ·
          refine ⟨41344683105462850652398787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27563122070308567101599191 41344683105462850652398787)
          ·
            refine ⟨62017024658194275978598181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41344683105462850652398787 62017024658194275978598181)
            ·
              refine ⟨11628192123411426745987159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62017024658194275978598181 11628192123411426745987159)
              ·
                refine ⟨17442288185117140118980739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628192123411426745987159 17442288185117140118980739)
                ·
                  refine ⟨26163432277675710178471109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17442288185117140118980739 26163432277675710178471109)
                  ·
                    refine ⟨4905643552064195658463333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26163432277675710178471109 4905643552064195658463333)
                    ·
                      refine ⟨919808166012036685961875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4905643552064195658463333 919808166012036685961875)
                      ·
                        rfl

theorem cell23_1791320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1791320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791320 prefixEnd_1791320 := by exact prefixLift 1791320
  have htrace : WordTrace (prefixWord ++ tailWord_1791320) baseStart_1791320 baseEnd_1791320 := by
    simpa [prefixWord, tailWord_1791320, baseEnd_1791320] using wordTrace_append hprefix tailTrace_1791320
  have hstable : (prefixWord ++ tailWord_1791320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791320).length < 2 ^ (prefixWord ++ tailWord_1791320).sum := by decide
  have hdescent : baseEnd_1791320 < baseStart_1791320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791357 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1791357 : Nat := 118140960795 + 1791357 * 2 ^ 59
def prefixEnd_1791357 : Nat := 4983230072969 + 3 ^ 40 * 1791357 * 2
def baseEnd_1791357 : Nat := 919827164796253041199205

theorem tailTrace_1791357 : CollatzResearch.WordTrace tailWord_1791357 prefixEnd_1791357 919827164796253041199205 := by
  unfold tailWord_1791357
  simp only [CollatzResearch.WordTrace]
  refine ⟨65336157371227003263628325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43557438247484668842418883 65336157371227003263628325)
  ·
    refine ⟨12250529507105063111930311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65336157371227003263628325 12250529507105063111930311)
    ·
      refine ⟨18375794260657594667895467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250529507105063111930311 18375794260657594667895467)
      ·
        refine ⟨27563691390986392001843201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375794260657594667895467 27563691390986392001843201)
        ·
          refine ⟨20672768543239794001382401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27563691390986392001843201 20672768543239794001382401)
          ·
            refine ⟨15504576407429845501036801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20672768543239794001382401 15504576407429845501036801)
            ·
              refine ⟨11628432305572384125777601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504576407429845501036801 11628432305572384125777601)
              ·
                refine ⟨8721324229179288094333201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11628432305572384125777601 8721324229179288094333201)
                ·
                  refine ⟨6540993171884466070749901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8721324229179288094333201 6540993171884466070749901)
                  ·
                    refine ⟨2452872439456674776531213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6540993171884466070749901 2452872439456674776531213)
                    ·
                      refine ⟨919827164796253041199205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2452872439456674776531213 919827164796253041199205)
                      ·
                        rfl

theorem cell23_1791357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1791357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791357 prefixEnd_1791357 := by exact prefixLift 1791357
  have htrace : WordTrace (prefixWord ++ tailWord_1791357) baseStart_1791357 baseEnd_1791357 := by
    simpa [prefixWord, tailWord_1791357, baseEnd_1791357] using wordTrace_append hprefix tailTrace_1791357
  have hstable : (prefixWord ++ tailWord_1791357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791357).length < 2 ^ (prefixWord ++ tailWord_1791357).sum := by decide
  have hdescent : baseEnd_1791357 < baseStart_1791357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791364 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1791364 : Nat := 118140960795 + 1791364 * 2 ^ 59
def prefixEnd_1791364 : Nat := 4983230072969 + 3 ^ 40 * 1791364 * 2
def baseEnd_1791364 : Nat := 102203417684537168201297

theorem tailTrace_1791364 : CollatzResearch.WordTrace tailWord_1791364 prefixEnd_1791364 102203417684537168201297 := by
  unfold tailWord_1791364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32668206341100821729566573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43557608454801095639422097 32668206341100821729566573)
  ·
    refine ⟨12250577377912808148587465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32668206341100821729566573 12250577377912808148587465)
    ·
      refine ⟨9187933033434606111440599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12250577377912808148587465 9187933033434606111440599)
      ·
        refine ⟨13781899550151909167160899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9187933033434606111440599 13781899550151909167160899)
        ·
          refine ⟨20672849325227863750741349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13781899550151909167160899 20672849325227863750741349)
          ·
            refine ⟨3876159248480224453264003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20672849325227863750741349 3876159248480224453264003)
            ·
              refine ⟨5814238872720336679896005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876159248480224453264003 5814238872720336679896005)
              ·
                refine ⟨1090169788635063127480501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5814238872720336679896005 1090169788635063127480501)
                ·
                  refine ⟨102203417684537168201297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090169788635063127480501 102203417684537168201297)
                  ·
                    rfl

theorem cell23_1791364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1791364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791364 prefixEnd_1791364 := by exact prefixLift 1791364
  have htrace : WordTrace (prefixWord ++ tailWord_1791364) baseStart_1791364 baseEnd_1791364 := by
    simpa [prefixWord, tailWord_1791364, baseEnd_1791364] using wordTrace_append hprefix tailTrace_1791364
  have hstable : (prefixWord ++ tailWord_1791364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791364).length < 2 ^ (prefixWord ++ tailWord_1791364).sum := by decide
  have hdescent : baseEnd_1791364 < baseStart_1791364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791394 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1791394 : Nat := 118140960795 + 1791394 * 2 ^ 59
def prefixEnd_1791394 : Nat := 4983230072969 + 3 ^ 40 * 1791394 * 2
def baseEnd_1791394 : Nat := 306615387860156465478845

theorem tailTrace_1791394 : CollatzResearch.WordTrace tailWord_1791394 prefixEnd_1791394 306615387860156465478845 := by
  unfold tailWord_1791394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16334376718023239645681309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43558337914728639055150157 16334376718023239645681309)
  ·
    refine ⟨6125391269258714867130491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16334376718023239645681309 6125391269258714867130491)
    ·
      refine ⟨9188086903888072300695737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125391269258714867130491 9188086903888072300695737)
      ·
        refine ⟨6891065177916054225521803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9188086903888072300695737 6891065177916054225521803)
        ·
          refine ⟨10336597766874081338282705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891065177916054225521803 10336597766874081338282705)
          ·
            refine ⟨7752448325155561003712029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336597766874081338282705 7752448325155561003712029)
            ·
              refine ⟨2907168121933335376392011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7752448325155561003712029 2907168121933335376392011)
              ·
                refine ⟨4360752182900003064588017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907168121933335376392011 4360752182900003064588017)
                ·
                  refine ⟨3270564137175002298441013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360752182900003064588017 3270564137175002298441013)
                  ·
                    refine ⟨306615387860156465478845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3270564137175002298441013 306615387860156465478845)
                    ·
                      rfl

theorem cell23_1791394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1791394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791394 prefixEnd_1791394 := by exact prefixLift 1791394
  have htrace : WordTrace (prefixWord ++ tailWord_1791394) baseStart_1791394 baseEnd_1791394 := by
    simpa [prefixWord, tailWord_1791394, baseEnd_1791394] using wordTrace_append hprefix tailTrace_1791394
  have hstable : (prefixWord ++ tailWord_1791394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791394).length < 2 ^ (prefixWord ++ tailWord_1791394).sum := by decide
  have hdescent : baseEnd_1791394 < baseStart_1791394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791397 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1791397 : Nat := 118140960795 + 1791397 * 2 ^ 59
def prefixEnd_1791397 : Nat := 4983230072969 + 3 ^ 40 * 1791397 * 2
def baseEnd_1791397 : Nat := 919847704022432884699021

theorem tailTrace_1791397 : CollatzResearch.WordTrace tailWord_1791397 prefixEnd_1791397 919847704022432884699021 := by
  unfold tailWord_1791397
  simp only [CollatzResearch.WordTrace]
  refine ⟨65337616291082090095084445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43558410860721393396722963 65337616291082090095084445)
  ·
    refine ⟨24501606109155783785656667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65337616291082090095084445 24501606109155783785656667)
    ·
      refine ⟨36752409163733675678485001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24501606109155783785656667 36752409163733675678485001)
      ·
        refine ⟨27564306872800256758863751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36752409163733675678485001 27564306872800256758863751)
        ·
          refine ⟨41346460309200385138295627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27564306872800256758863751 41346460309200385138295627)
          ·
            refine ⟨62019690463800577707443441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41346460309200385138295627 62019690463800577707443441)
            ·
              refine ⟨46514767847850433280582581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62019690463800577707443441 46514767847850433280582581)
              ·
                refine ⟨4360759485735978120054617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46514767847850433280582581 4360759485735978120054617)
                ·
                  refine ⟨3270569614301983590040963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360759485735978120054617 3270569614301983590040963)
                  ·
                    refine ⟨4905854421452975385061445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270569614301983590040963 4905854421452975385061445)
                    ·
                      refine ⟨919847704022432884699021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4905854421452975385061445 919847704022432884699021)
                      ·
                        rfl

theorem cell23_1791397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1791397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791397 prefixEnd_1791397 := by exact prefixLift 1791397
  have htrace : WordTrace (prefixWord ++ tailWord_1791397) baseStart_1791397 baseEnd_1791397 := by
    simpa [prefixWord, tailWord_1791397, baseEnd_1791397] using wordTrace_append hprefix tailTrace_1791397
  have hstable : (prefixWord ++ tailWord_1791397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791397).length < 2 ^ (prefixWord ++ tailWord_1791397).sum := by decide
  have hdescent : baseEnd_1791397 < baseStart_1791397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791426 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1791426 : Nat := 118140960795 + 1791426 * 2 ^ 59
def prefixEnd_1791426 : Nat := 4983230072969 + 3 ^ 40 * 1791426 * 2
def baseEnd_1791426 : Nat := 919862594961413271236389

theorem tailTrace_1791426 : CollatzResearch.WordTrace tailWord_1791426 prefixEnd_1791426 919862594961413271236389 := by
  unfold tailWord_1791426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16334668501994257011972533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43559116005318018698593421 16334668501994257011972533)
  ·
    refine ⟨1531375172061961594872425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16334668501994257011972533 1531375172061961594872425)
    ·
      refine ⟨1148531379046471196154319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1531375172061961594872425 1148531379046471196154319)
      ·
        refine ⟨1722797068569706794231479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148531379046471196154319 1722797068569706794231479)
        ·
          refine ⟨2584195602854560191347219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722797068569706794231479 2584195602854560191347219)
          ·
            refine ⟨3876293404281840287020829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584195602854560191347219 3876293404281840287020829)
            ·
              refine ⟨1453610026605690107632811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3876293404281840287020829 1453610026605690107632811)
              ·
                refine ⟨2180415039908535161449217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453610026605690107632811 2180415039908535161449217)
                ·
                  refine ⟨1635311279931401371086913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180415039908535161449217 1635311279931401371086913)
                  ·
                    refine ⟨1226483459948551028315185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1635311279931401371086913 1226483459948551028315185)
                    ·
                      refine ⟨919862594961413271236389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1226483459948551028315185 919862594961413271236389)
                      ·
                        rfl

theorem cell23_1791426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1791426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791426 prefixEnd_1791426 := by exact prefixLift 1791426
  have htrace : WordTrace (prefixWord ++ tailWord_1791426) baseStart_1791426 baseEnd_1791426 := by
    simpa [prefixWord, tailWord_1791426, baseEnd_1791426] using wordTrace_append hprefix tailTrace_1791426
  have hstable : (prefixWord ++ tailWord_1791426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791426).length < 2 ^ (prefixWord ++ tailWord_1791426).sum := by decide
  have hdescent : baseEnd_1791426 < baseStart_1791426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791497 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_1791497 : Nat := 118140960795 + 1791497 * 2 ^ 59
def prefixEnd_1791497 : Nat := 4983230072969 + 3 ^ 40 * 1791497 * 2
def baseEnd_1791497 : Nat := 306633017362627497816187

theorem tailTrace_1791497 : CollatzResearch.WordTrace tailWord_1791497 prefixEnd_1791497 306633017362627497816187 := by
  unfold tailWord_1791497
  simp only [CollatzResearch.WordTrace]
  refine ⟨65341263590719807173724745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43560842393813204782483163 65341263590719807173724745)
  ·
    refine ⟨49005947693039855380293559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65341263590719807173724745 49005947693039855380293559)
    ·
      refine ⟨73508921539559783070440339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49005947693039855380293559 73508921539559783070440339)
      ·
        refine ⟨110263382309339674605660509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73508921539559783070440339 110263382309339674605660509)
        ·
          refine ⟨41348768366002377977122691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110263382309339674605660509 41348768366002377977122691)
          ·
            refine ⟨62023152549003566965684037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41348768366002377977122691 62023152549003566965684037)
            ·
              refine ⟨11629341102938168806065757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62023152549003566965684037 11629341102938168806065757)
              ·
                refine ⟨4361002913601813302274659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11629341102938168806065757 4361002913601813302274659)
                ·
                  refine ⟨6541504370402719953411989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361002913601813302274659 6541504370402719953411989)
                  ·
                    refine ⟨306633017362627497816187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6541504370402719953411989 306633017362627497816187)
                    ·
                      rfl

theorem cell23_1791497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_1791497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791497 prefixEnd_1791497 := by exact prefixLift 1791497
  have htrace : WordTrace (prefixWord ++ tailWord_1791497) baseStart_1791497 baseEnd_1791497 := by
    simpa [prefixWord, tailWord_1791497, baseEnd_1791497] using wordTrace_append hprefix tailTrace_1791497
  have hstable : (prefixWord ++ tailWord_1791497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791497).length < 2 ^ (prefixWord ++ tailWord_1791497).sum := by decide
  have hdescent : baseEnd_1791497 < baseStart_1791497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791527 : List Nat := [1, 1, 7, 14]
def baseStart_1791527 : Nat := 118140960795 + 1791527 * 2 ^ 59
def prefixEnd_1791527 : Nat := 4983230072969 + 3 ^ 40 * 1791527 * 2
def baseEnd_1791527 : Nat := 420628466624379230029

theorem tailTrace_1791527 : CollatzResearch.WordTrace tailWord_1791527 prefixEnd_1791527 420628466624379230029 := by
  unfold tailWord_1791527
  simp only [CollatzResearch.WordTrace]
  refine ⟨65342357780611122297316835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43561571853740748198211223 65342357780611122297316835)
  ·
    refine ⟨98013536670916683445975253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65342357780611122297316835 98013536670916683445975253)
    ·
      refine ⟨2297192265724609768265045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98013536670916683445975253 2297192265724609768265045)
      ·
        refine ⟨420628466624379230029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2297192265724609768265045 420628466624379230029)
        ·
          rfl

theorem cell23_1791527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 14].length) (baseStart_1791527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791527 prefixEnd_1791527 := by exact prefixLift 1791527
  have htrace : WordTrace (prefixWord ++ tailWord_1791527) baseStart_1791527 baseEnd_1791527 := by
    simpa [prefixWord, tailWord_1791527, baseEnd_1791527] using wordTrace_append hprefix tailTrace_1791527
  have hstable : (prefixWord ++ tailWord_1791527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791527).length < 2 ^ (prefixWord ++ tailWord_1791527).sum := by decide
  have hdescent : baseEnd_1791527 < baseStart_1791527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791544 : List Nat := [2, 1, 2, 1, 4, 4, 1, 8]
def baseStart_1791544 : Nat := 118140960795 + 1791544 * 2 ^ 59
def prefixEnd_1791544 : Nat := 4983230072969 + 3 ^ 40 * 1791544 * 2
def baseEnd_1791544 : Nat := 34071229099209029983735

theorem tailTrace_1791544 : CollatzResearch.WordTrace tailWord_1791544 prefixEnd_1791544 34071229099209029983735 := by
  unfold tailWord_1791544
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671488910774767100342843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43561985214366356133790457 32671488910774767100342843)
  ·
    refine ⟨49007233366162150650514265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671488910774767100342843 49007233366162150650514265)
    ·
      refine ⟨36755425024621612987885699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49007233366162150650514265 36755425024621612987885699)
      ·
        refine ⟨55133137536932419481828549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36755425024621612987885699 55133137536932419481828549)
        ·
          refine ⟨10337463288174828652842853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55133137536932419481828549 10337463288174828652842853)
          ·
            refine ⟨1938274366532780372408035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10337463288174828652842853 1938274366532780372408035)
            ·
              refine ⟨2907411549799170558612053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938274366532780372408035 2907411549799170558612053)
              ·
                refine ⟨34071229099209029983735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2907411549799170558612053 34071229099209029983735)
                ·
                  rfl

theorem cell23_1791544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 8].length) (baseStart_1791544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791544 prefixEnd_1791544 := by exact prefixLift 1791544
  have htrace : WordTrace (prefixWord ++ tailWord_1791544) baseStart_1791544 baseEnd_1791544 := by
    simpa [prefixWord, tailWord_1791544, baseEnd_1791544] using wordTrace_append hprefix tailTrace_1791544
  have hstable : (prefixWord ++ tailWord_1791544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791544).length < 2 ^ (prefixWord ++ tailWord_1791544).sum := by decide
  have hdescent : baseEnd_1791544 < baseStart_1791544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791557 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1791557 : Nat := 118140960795 + 1791557 * 2 ^ 59
def prefixEnd_1791557 : Nat := 4983230072969 + 3 ^ 40 * 1791557 * 2
def baseEnd_1791557 : Nat := 306643286975717419566095

theorem tailTrace_1791557 : CollatzResearch.WordTrace tailWord_1791557 prefixEnd_1791557 306643286975717419566095 := by
  unfold tailWord_1791557
  simp only [CollatzResearch.WordTrace]
  refine ⟨65343451970502437420908925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43562301313668291613939283 65343451970502437420908925)
  ·
    refine ⟨24503794488938414032840847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65343451970502437420908925 24503794488938414032840847)
    ·
      refine ⟨36755691733407621049261271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24503794488938414032840847 36755691733407621049261271)
      ·
        refine ⟨55133537600111431573891907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36755691733407621049261271 55133537600111431573891907)
        ·
          refine ⟨82700306400167147360837861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55133537600111431573891907 82700306400167147360837861)
          ·
            refine ⟨15506307450031340130157099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82700306400167147360837861 15506307450031340130157099)
            ·
              refine ⟨23259461175047010195235649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506307450031340130157099 23259461175047010195235649)
              ·
                refine ⟨17444595881285257646426737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23259461175047010195235649 17444595881285257646426737)
                ·
                  refine ⟨13083446910963943234820053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17444595881285257646426737 13083446910963943234820053)
                  ·
                    refine ⟨306643286975717419566095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13083446910963943234820053 306643286975717419566095)
                    ·
                      rfl

theorem cell23_1791557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1791557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791557 prefixEnd_1791557 := by exact prefixLift 1791557
  have htrace : WordTrace (prefixWord ++ tailWord_1791557) baseStart_1791557 baseEnd_1791557 := by
    simpa [prefixWord, tailWord_1791557, baseEnd_1791557] using wordTrace_append hprefix tailTrace_1791557
  have hstable : (prefixWord ++ tailWord_1791557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791557).length < 2 ^ (prefixWord ++ tailWord_1791557).sum := by decide
  have hdescent : baseEnd_1791557 < baseStart_1791557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791567 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_1791567 : Nat := 118140960795 + 1791567 * 2 ^ 59
def prefixEnd_1791567 : Nat := 4983230072969 + 3 ^ 40 * 1791567 * 2
def baseEnd_1791567 : Nat := 919934995733697219573239

theorem tailTrace_1791567 : CollatzResearch.WordTrace tailWord_1791567 prefixEnd_1791567 919934995733697219573239 := by
  unfold tailWord_1791567
  simp only [CollatzResearch.WordTrace]
  refine ⟨65343816700466209128772955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43562544466977472752515303 65343816700466209128772955)
  ·
    refine ⟨98015725050699313693159433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65343816700466209128772955 98015725050699313693159433)
    ·
      refine ⟨73511793788024485269869575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98015725050699313693159433 73511793788024485269869575)
      ·
        refine ⟨110267690682036727904804363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73511793788024485269869575 110267690682036727904804363)
        ·
          refine ⟨165401536023055091857206545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110267690682036727904804363 165401536023055091857206545)
          ·
            refine ⟨124051152017291318892904909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165401536023055091857206545 124051152017291318892904909)
            ·
              refine ⟨46519182006484244584839341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124051152017291318892904909 46519182006484244584839341)
              ·
                refine ⟨17444693252431591719314753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46519182006484244584839341 17444693252431591719314753)
                ·
                  refine ⟨13083519939323693789486065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17444693252431591719314753 13083519939323693789486065)
                  ·
                    refine ⟨9812639954492770342114549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13083519939323693789486065 9812639954492770342114549)
                    ·
                      refine ⟨919934995733697219573239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9812639954492770342114549 919934995733697219573239)
                      ·
                        rfl

theorem cell23_1791567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_1791567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791567 prefixEnd_1791567 := by exact prefixLift 1791567
  have htrace : WordTrace (prefixWord ++ tailWord_1791567) baseStart_1791567 baseEnd_1791567 := by
    simpa [prefixWord, tailWord_1791567, baseEnd_1791567] using wordTrace_append hprefix tailTrace_1791567
  have hstable : (prefixWord ++ tailWord_1791567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791567).length < 2 ^ (prefixWord ++ tailWord_1791567).sum := by decide
  have hdescent : baseEnd_1791567 < baseStart_1791567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791588 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_1791588 : Nat := 118140960795 + 1791588 * 2 ^ 59
def prefixEnd_1791588 : Nat := 4983230072969 + 3 ^ 40 * 1791588 * 2
def baseEnd_1791588 : Nat := 919945778827441637410643

theorem tailTrace_1791588 : CollatzResearch.WordTrace tailWord_1791588 prefixEnd_1791588 919945778827441637410643 := by
  unfold tailWord_1791588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672291316695064857643709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43563055088926753143524945 32672291316695064857643709)
  ·
    refine ⟨12252109243760649321616391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32672291316695064857643709 12252109243760649321616391)
    ·
      refine ⟨18378163865640973982424587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252109243760649321616391 18378163865640973982424587)
      ·
        refine ⟨27567245798461460973636881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378163865640973982424587 27567245798461460973636881)
        ·
          refine ⟨20675434348846095730227661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27567245798461460973636881 20675434348846095730227661)
          ·
            refine ⟨7753287880817285898835373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20675434348846095730227661 7753287880817285898835373)
            ·
              refine ⟨2907482955306482212063265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7753287880817285898835373 2907482955306482212063265)
              ·
                refine ⟨2180612216479861659047449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907482955306482212063265 2180612216479861659047449)
                ·
                  refine ⟨1635459162359896244285587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180612216479861659047449 1635459162359896244285587)
                  ·
                    refine ⟨2453188743539844366428381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635459162359896244285587 2453188743539844366428381)
                    ·
                      refine ⟨919945778827441637410643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453188743539844366428381 919945778827441637410643)
                      ·
                        rfl

theorem cell23_1791588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_1791588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791588 prefixEnd_1791588 := by exact prefixLift 1791588
  have htrace : WordTrace (prefixWord ++ tailWord_1791588) baseStart_1791588 baseEnd_1791588 := by
    simpa [prefixWord, tailWord_1791588, baseEnd_1791588] using wordTrace_append hprefix tailTrace_1791588
  have hstable : (prefixWord ++ tailWord_1791588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791588).length < 2 ^ (prefixWord ++ tailWord_1791588).sum := by decide
  have hdescent : baseEnd_1791588 < baseStart_1791588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791656 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1791656 : Nat := 118140960795 + 1791656 * 2 ^ 59
def prefixEnd_1791656 : Nat := 4983230072969 + 3 ^ 40 * 1791656 * 2
def baseEnd_1791656 : Nat := 919980695511947371360331

theorem tailTrace_1791656 : CollatzResearch.WordTrace tailWord_1791656 prefixEnd_1791656 919980695511947371360331 := by
  unfold tailWord_1791656
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673531398571888664381411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43564708531429184885841881 32673531398571888664381411)
  ·
    refine ⟨49010297097857832996572117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32673531398571888664381411 49010297097857832996572117)
    ·
      refine ⟨1148678838231042960857159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 49010297097857832996572117 1148678838231042960857159)
      ·
        refine ⟨1723018257346564441285739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148678838231042960857159 1723018257346564441285739)
        ·
          refine ⟨2584527386019846661928609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723018257346564441285739 2584527386019846661928609)
          ·
            refine ⟨1938395539514884996446457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584527386019846661928609 1938395539514884996446457)
            ·
              refine ⟨1453796654636163747334843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938395539514884996446457 1453796654636163747334843)
              ·
                refine ⟨2180694981954245621002265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453796654636163747334843 2180694981954245621002265)
                ·
                  refine ⟨1635521236465684215751699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180694981954245621002265 1635521236465684215751699)
                  ·
                    refine ⟨2453281854698526323627549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635521236465684215751699 2453281854698526323627549)
                    ·
                      refine ⟨919980695511947371360331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453281854698526323627549 919980695511947371360331)
                      ·
                        rfl

theorem cell23_1791656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1791656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791656 prefixEnd_1791656 := by exact prefixLift 1791656
  have htrace : WordTrace (prefixWord ++ tailWord_1791656) baseStart_1791656 baseEnd_1791656 := by
    simpa [prefixWord, tailWord_1791656, baseEnd_1791656] using wordTrace_append hprefix tailTrace_1791656
  have hstable : (prefixWord ++ tailWord_1791656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791656).length < 2 ^ (prefixWord ++ tailWord_1791656).sum := by decide
  have hdescent : baseEnd_1791656 < baseStart_1791656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791661 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1791661 : Nat := 118140960795 + 1791661 * 2 ^ 59
def prefixEnd_1791661 : Nat := 4983230072969 + 3 ^ 40 * 1791661 * 2
def baseEnd_1791661 : Nat := 919983262915219851797807

theorem tailTrace_1791661 : CollatzResearch.WordTrace tailWord_1791661 prefixEnd_1791661 919983262915219851797807 := by
  unfold tailWord_1791661
  simp only [CollatzResearch.WordTrace]
  refine ⟨65347245162125663182694837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43564830108083775455129891 65347245162125663182694837)
  ·
    refine ⟨6126304233949280923377641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65347245162125663182694837 6126304233949280923377641)
    ·
      refine ⟨4594728175461960692533231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126304233949280923377641 4594728175461960692533231)
      ·
        refine ⟨6892092263192941038799847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594728175461960692533231 6892092263192941038799847)
        ·
          refine ⟨10338138394789411558199771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892092263192941038799847 10338138394789411558199771)
          ·
            refine ⟨15507207592184117337299657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338138394789411558199771 15507207592184117337299657)
            ·
              refine ⟨11630405694138088002974743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15507207592184117337299657 11630405694138088002974743)
              ·
                refine ⟨17445608541207132004462115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630405694138088002974743 17445608541207132004462115)
                ·
                  refine ⟨26168412811810698006693173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17445608541207132004462115 26168412811810698006693173)
                  ·
                    refine ⟨2453288701107252938127485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26168412811810698006693173 2453288701107252938127485)
                    ·
                      refine ⟨919983262915219851797807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453288701107252938127485 919983262915219851797807)
                      ·
                        rfl

theorem cell23_1791661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1791661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791661 prefixEnd_1791661 := by exact prefixLift 1791661
  have htrace : WordTrace (prefixWord ++ tailWord_1791661) baseStart_1791661 baseEnd_1791661 := by
    simpa [prefixWord, tailWord_1791661, baseEnd_1791661] using wordTrace_append hprefix tailTrace_1791661
  have hstable : (prefixWord ++ tailWord_1791661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791661).length < 2 ^ (prefixWord ++ tailWord_1791661).sum := by decide
  have hdescent : baseEnd_1791661 < baseStart_1791661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791702 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1791702 : Nat := 118140960795 + 1791702 * 2 ^ 59
def prefixEnd_1791702 : Nat := 4983230072969 + 3 ^ 40 * 1791702 * 2
def baseEnd_1791702 : Nat := 102222701735783799042791

theorem tailTrace_1791702 : CollatzResearch.WordTrace tailWord_1791702 prefixEnd_1791702 102222701735783799042791 := by
  unfold tailWord_1791702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084296284686070449058585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43565827036651418123291573 4084296284686070449058585)
  ·
    refine ⟨3063222213514552836793939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4084296284686070449058585 3063222213514552836793939)
    ·
      refine ⟨4594833320271829255190909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063222213514552836793939 4594833320271829255190909)
      ·
        refine ⟨1723062495101935970696591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4594833320271829255190909 1723062495101935970696591)
        ·
          refine ⟨2584593742652903956044887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723062495101935970696591 2584593742652903956044887)
          ·
            refine ⟨3876890613979355934067331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584593742652903956044887 3876890613979355934067331)
            ·
              refine ⟨5815335920969033901100997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876890613979355934067331 5815335920969033901100997)
              ·
                refine ⟨1090375485181693856456437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5815335920969033901100997 1090375485181693856456437)
                ·
                  refine ⟨102222701735783799042791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090375485181693856456437 102222701735783799042791)
                  ·
                    rfl

theorem cell23_1791702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1791702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791702 prefixEnd_1791702 := by exact prefixLift 1791702
  have htrace : WordTrace (prefixWord ++ tailWord_1791702) baseStart_1791702 baseEnd_1791702 := by
    simpa [prefixWord, tailWord_1791702, baseEnd_1791702] using wordTrace_append hprefix tailTrace_1791702
  have hstable : (prefixWord ++ tailWord_1791702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791702).length < 2 ^ (prefixWord ++ tailWord_1791702).sum := by decide
  have hdescent : baseEnd_1791702 < baseStart_1791702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791704 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1791704 : Nat := 118140960795 + 1791704 * 2 ^ 59
def prefixEnd_1791704 : Nat := 4983230072969 + 3 ^ 40 * 1791704 * 2
def baseEnd_1791704 : Nat := 920005342583363183560109

theorem tailTrace_1791704 : CollatzResearch.WordTrace tailWord_1791704 prefixEnd_1791704 920005342583363183560109 := by
  unfold tailWord_1791704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674406750484940763255083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43565875667313254351006777 32674406750484940763255083)
  ·
    refine ⟨49011610125727411144882625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32674406750484940763255083 49011610125727411144882625)
    ·
      refine ⟨36758707594295558358661969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49011610125727411144882625 36758707594295558358661969)
      ·
        refine ⟨27569030695721668768996477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36758707594295558358661969 27569030695721668768996477)
        ·
          refine ⟨10338386510895625788373679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27569030695721668768996477 10338386510895625788373679)
          ·
            refine ⟨15507579766343438682560519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338386510895625788373679 15507579766343438682560519)
            ·
              refine ⟨23261369649515158023840779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15507579766343438682560519 23261369649515158023840779)
              ·
                refine ⟨34892054474272737035761169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23261369649515158023840779 34892054474272737035761169)
                ·
                  refine ⟨26169040855704552776820877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34892054474272737035761169 26169040855704552776820877)
                  ·
                    refine ⟨9813390320889207291307829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26169040855704552776820877 9813390320889207291307829)
                    ·
                      refine ⟨920005342583363183560109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9813390320889207291307829 920005342583363183560109)
                      ·
                        rfl

theorem cell23_1791704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1791704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791704 prefixEnd_1791704 := by exact prefixLift 1791704
  have htrace : WordTrace (prefixWord ++ tailWord_1791704) baseStart_1791704 baseEnd_1791704 := by
    simpa [prefixWord, tailWord_1791704, baseEnd_1791704] using wordTrace_append hprefix tailTrace_1791704
  have hstable : (prefixWord ++ tailWord_1791704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791704).length < 2 ^ (prefixWord ++ tailWord_1791704).sum := by decide
  have hdescent : baseEnd_1791704 < baseStart_1791704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791711 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 3, 4]
def baseStart_1791711 : Nat := 118140960795 + 1791711 * 2 ^ 59
def prefixEnd_1791711 : Nat := 4983230072969 + 3 ^ 40 * 1791711 * 2
def baseEnd_1791711 : Nat := 306669645649314885390859

theorem tailTrace_1791711 : CollatzResearch.WordTrace tailWord_1791711 prefixEnd_1791711 306669645649314885390859 := by
  unfold tailWord_1791711
  simp only [CollatzResearch.WordTrace]
  refine ⟨65349068811944521722014987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43566045874629681148009991 65349068811944521722014987)
  ·
    refine ⟨98023603217916782583022481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65349068811944521722014987 98023603217916782583022481)
    ·
      refine ⟨73517702413437586937266861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98023603217916782583022481 73517702413437586937266861)
      ·
        refine ⟨27569138405039095101475073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73517702413437586937266861 27569138405039095101475073)
        ·
          refine ⟨20676853803779321326106305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569138405039095101475073 20676853803779321326106305)
          ·
            refine ⟨15507640352834490994579729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20676853803779321326106305 15507640352834490994579729)
            ·
              refine ⟨11630730264625868245934797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15507640352834490994579729 11630730264625868245934797)
              ·
                refine ⟨4361523849234700592225549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11630730264625868245934797 4361523849234700592225549)
                ·
                  refine ⟨1635571443463012722084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4361523849234700592225549 1635571443463012722084581)
                  ·
                    refine ⟨306669645649314885390859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635571443463012722084581 306669645649314885390859)
                    ·
                      rfl

theorem cell23_1791711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_1791711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791711 prefixEnd_1791711 := by exact prefixLift 1791711
  have htrace : WordTrace (prefixWord ++ tailWord_1791711) baseStart_1791711 baseEnd_1791711 := by
    simpa [prefixWord, tailWord_1791711, baseEnd_1791711] using wordTrace_append hprefix tailTrace_1791711
  have hstable : (prefixWord ++ tailWord_1791711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791711).length < 2 ^ (prefixWord ++ tailWord_1791711).sum := by decide
  have hdescent : baseEnd_1791711 < baseStart_1791711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791732 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1791732 : Nat := 118140960795 + 1791732 * 2 ^ 59
def prefixEnd_1791732 : Nat := 4983230072969 + 3 ^ 40 * 1791732 * 2
def baseEnd_1791732 : Nat := 306673240013896358003327

theorem tailTrace_1791732 : CollatzResearch.WordTrace tailWord_1791732 prefixEnd_1791732 306673240013896358003327 := by
  unfold tailWord_1791732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674917372434221154264725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43566556496578961539019633 32674917372434221154264725)
  ·
    refine ⟨1531636751832854116606159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32674917372434221154264725 1531636751832854116606159)
    ·
      refine ⟨2297455127749281174909239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531636751832854116606159 2297455127749281174909239)
      ·
        refine ⟨3446182691623921762363859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297455127749281174909239 3446182691623921762363859)
        ·
          refine ⟨5169274037435882643545789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446182691623921762363859 5169274037435882643545789)
          ·
            refine ⟨1938477764038455991329671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5169274037435882643545789 1938477764038455991329671)
            ·
              refine ⟨2907716646057683986994507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938477764038455991329671 2907716646057683986994507)
              ·
                refine ⟨4361574969086525980491761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907716646057683986994507 4361574969086525980491761)
                ·
                  refine ⟨3271181226814894485368821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361574969086525980491761 3271181226814894485368821)
                  ·
                    refine ⟨306673240013896358003327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3271181226814894485368821 306673240013896358003327)
                    ·
                      rfl

theorem cell23_1791732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1791732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791732 prefixEnd_1791732 := by exact prefixLift 1791732
  have htrace : WordTrace (prefixWord ++ tailWord_1791732) baseStart_1791732 baseEnd_1791732 := by
    simpa [prefixWord, tailWord_1791732, baseEnd_1791732] using wordTrace_append hprefix tailTrace_1791732
  have hstable : (prefixWord ++ tailWord_1791732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791732).length < 2 ^ (prefixWord ++ tailWord_1791732).sum := by decide
  have hdescent : baseEnd_1791732 < baseStart_1791732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791762 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1791762 : Nat := 118140960795 + 1791762 * 2 ^ 59
def prefixEnd_1791762 : Nat := 4983230072969 + 3 ^ 40 * 1791762 * 2
def baseEnd_1791762 : Nat := 306678374820441318878281

theorem tailTrace_1791762 : CollatzResearch.WordTrace tailWord_1791762 prefixEnd_1791762 306678374820441318878281 := by
  unfold tailWord_1791762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337732233689939358030385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43567285956506504954747693 16337732233689939358030385)
  ·
    refine ⟨12253299175267454518522789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16337732233689939358030385 12253299175267454518522789)
    ·
      refine ⟨2297493595362647722223023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12253299175267454518522789 2297493595362647722223023)
      ·
        refine ⟨3446240393043971583334535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297493595362647722223023 3446240393043971583334535)
        ·
          refine ⟨5169360589565957375001803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446240393043971583334535 5169360589565957375001803)
          ·
            refine ⟨7754040884348936062502705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169360589565957375001803 7754040884348936062502705)
            ·
              refine ⟨5815530663261702046877029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754040884348936062502705 5815530663261702046877029)
              ·
                refine ⟨1090411999361569133789443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5815530663261702046877029 1090411999361569133789443)
                ·
                  refine ⟨1635617999042353700684165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090411999361569133789443 1635617999042353700684165)
                  ·
                    refine ⟨306678374820441318878281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635617999042353700684165 306678374820441318878281)
                    ·
                      rfl

theorem cell23_1791762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1791762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791762 prefixEnd_1791762 := by exact prefixLift 1791762
  have htrace : WordTrace (prefixWord ++ tailWord_1791762) baseStart_1791762 baseEnd_1791762 := by
    simpa [prefixWord, tailWord_1791762, baseEnd_1791762] using wordTrace_append hprefix tailTrace_1791762
  have hstable : (prefixWord ++ tailWord_1791762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791762).length < 2 ^ (prefixWord ++ tailWord_1791762).sum := by decide
  have hdescent : baseEnd_1791762 < baseStart_1791762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791768 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1791768 : Nat := 118140960795 + 1791768 * 2 ^ 59
def prefixEnd_1791768 : Nat := 4983230072969 + 3 ^ 40 * 1791768 * 2
def baseEnd_1791768 : Nat := 920038205345250933159815

theorem tailTrace_1791768 : CollatzResearch.WordTrace tailWord_1791768 prefixEnd_1791768 920038205345250933159815 := by
  unfold tailWord_1791768
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675573886369010228419979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43567431848492013637893305 32675573886369010228419979)
  ·
    refine ⟨49013360829553515342629969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32675573886369010228419979 49013360829553515342629969)
    ·
      refine ⟨36760020622165136506972477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49013360829553515342629969 36760020622165136506972477)
      ·
        refine ⟨13785007733311926190114679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36760020622165136506972477 13785007733311926190114679)
        ·
          refine ⟨20677511599967889285172019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13785007733311926190114679 20677511599967889285172019)
          ·
            refine ⟨31016267399951833927758029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20677511599967889285172019 31016267399951833927758029)
            ·
              refine ⟨11631100274981937722909261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31016267399951833927758029 11631100274981937722909261)
              ·
                refine ⟨4361662603118226646090973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11631100274981937722909261 4361662603118226646090973)
                ·
                  refine ⟨1635623476169334992284115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4361662603118226646090973 1635623476169334992284115)
                  ·
                    refine ⟨2453435214254002488426173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635623476169334992284115 2453435214254002488426173)
                    ·
                      refine ⟨920038205345250933159815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453435214254002488426173 920038205345250933159815)
                      ·
                        rfl

theorem cell23_1791768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1791768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791768 prefixEnd_1791768 := by exact prefixLift 1791768
  have htrace : WordTrace (prefixWord ++ tailWord_1791768) baseStart_1791768 baseEnd_1791768 := by
    simpa [prefixWord, tailWord_1791768, baseEnd_1791768] using wordTrace_append hprefix tailTrace_1791768
  have hstable : (prefixWord ++ tailWord_1791768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791768).length < 2 ^ (prefixWord ++ tailWord_1791768).sum := by decide
  have hdescent : baseEnd_1791768 < baseStart_1791768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791778 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_1791778 : Nat := 118140960795 + 1791778 * 2 ^ 59
def prefixEnd_1791778 : Nat := 4983230072969 + 3 ^ 40 * 1791778 * 2
def baseEnd_1791778 : Nat := 920043340151795894034769

theorem tailTrace_1791778 : CollatzResearch.WordTrace tailWord_1791778 prefixEnd_1791778 920043340151795894034769 := by
  unfold tailWord_1791778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337878125675448041175997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43567675001801194776469325 16337878125675448041175997)
  ·
    refine ⟨6126704297128293015440999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16337878125675448041175997 6126704297128293015440999)
    ·
      refine ⟨9190056445692439523161499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126704297128293015440999 9190056445692439523161499)
      ·
        refine ⟨13785084668538659284742249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190056445692439523161499 13785084668538659284742249)
        ·
          refine ⟨10338813501403994463556687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13785084668538659284742249 10338813501403994463556687)
          ·
            refine ⟨15508220252105991695335031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338813501403994463556687 15508220252105991695335031)
            ·
              refine ⟨23262330378158987543002547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15508220252105991695335031 23262330378158987543002547)
              ·
                refine ⟨34893495567238481314503821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23262330378158987543002547 34893495567238481314503821)
                ·
                  refine ⟨13085060837714430492938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34893495567238481314503821 13085060837714430492938933)
                  ·
                    refine ⟨1226724453535727858713025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13085060837714430492938933 1226724453535727858713025)
                    ·
                      refine ⟨920043340151795894034769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1226724453535727858713025 920043340151795894034769)
                      ·
                        rfl

theorem cell23_1791778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_1791778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791778 prefixEnd_1791778 := by exact prefixLift 1791778
  have htrace : WordTrace (prefixWord ++ tailWord_1791778) baseStart_1791778 baseEnd_1791778 := by
    simpa [prefixWord, tailWord_1791778, baseEnd_1791778] using wordTrace_append hprefix tailTrace_1791778
  have hstable : (prefixWord ++ tailWord_1791778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791778).length < 2 ^ (prefixWord ++ tailWord_1791778).sum := by decide
  have hdescent : baseEnd_1791778 < baseStart_1791778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791788 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_1791788 : Nat := 118140960795 + 1791788 * 2 ^ 59
def prefixEnd_1791788 : Nat := 4983230072969 + 3 ^ 40 * 1791788 * 2
def baseEnd_1791788 : Nat := 306682824986113618303241

theorem tailTrace_1791788 : CollatzResearch.WordTrace tailWord_1791788 prefixEnd_1791788 306682824986113618303241 := by
  unfold tailWord_1791788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675938616332781936284009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43567918155110375915045345 32675938616332781936284009)
  ·
    refine ⟨24506953962249586452213007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32675938616332781936284009 24506953962249586452213007)
    ·
      refine ⟨36760430943374379678319511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24506953962249586452213007 36760430943374379678319511)
      ·
        refine ⟨55140646415061569517479267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36760430943374379678319511 55140646415061569517479267)
        ·
          refine ⟨82710969622592354276218901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55140646415061569517479267 82710969622592354276218901)
          ·
            refine ⟨3877076701059016606697761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82710969622592354276218901 3877076701059016606697761)
            ·
              refine ⟨2907807525794262455023321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877076701059016606697761 2907807525794262455023321)
              ·
                refine ⟨2180855644345696841267491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907807525794262455023321 2180855644345696841267491)
                ·
                  refine ⟨3271283466518545261901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180855644345696841267491 3271283466518545261901237)
                  ·
                    refine ⟨306682824986113618303241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3271283466518545261901237 306682824986113618303241)
                    ·
                      rfl

theorem cell23_1791788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_1791788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791788 prefixEnd_1791788 := by exact prefixLift 1791788
  have htrace : WordTrace (prefixWord ++ tailWord_1791788) baseStart_1791788 baseEnd_1791788 := by
    simpa [prefixWord, tailWord_1791788, baseEnd_1791788] using wordTrace_append hprefix tailTrace_1791788
  have hstable : (prefixWord ++ tailWord_1791788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791788).length < 2 ^ (prefixWord ++ tailWord_1791788).sum := by decide
  have hdescent : baseEnd_1791788 < baseStart_1791788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791802 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_1791802 : Nat := 118140960795 + 1791802 * 2 ^ 59
def prefixEnd_1791802 : Nat := 4983230072969 + 3 ^ 40 * 1791802 * 2
def baseEnd_1791802 : Nat := 920055663687503800134659

theorem tailTrace_1791802 : CollatzResearch.WordTrace tailWord_1791802 prefixEnd_1791802 920055663687503800134659 := by
  unfold tailWord_1791802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338096963653711065894415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43568258569743229509051773 16338096963653711065894415)
  ·
    refine ⟨24507145445480566598841623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16338096963653711065894415 24507145445480566598841623)
    ·
      refine ⟨36760718168220849898262435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507145445480566598841623 36760718168220849898262435)
      ·
        refine ⟨55141077252331274847393653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36760718168220849898262435 55141077252331274847393653)
        ·
          refine ⟨5169475992406057016943155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55141077252331274847393653 5169475992406057016943155)
          ·
            refine ⟨7754213988609085525414733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169475992406057016943155 7754213988609085525414733)
            ·
              refine ⟨2907830245728407072030525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7754213988609085525414733 2907830245728407072030525)
              ·
                refine ⟨1090436342148152652011447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2907830245728407072030525 1090436342148152652011447)
                ·
                  refine ⟨1635654513222228978017171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090436342148152652011447 1635654513222228978017171)
                  ·
                    refine ⟨2453481769833343467025757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635654513222228978017171 2453481769833343467025757)
                    ·
                      refine ⟨920055663687503800134659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453481769833343467025757 920055663687503800134659)
                      ·
                        rfl

theorem cell23_1791802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_1791802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791802 prefixEnd_1791802 := by exact prefixLift 1791802
  have htrace : WordTrace (prefixWord ++ tailWord_1791802) baseStart_1791802 baseEnd_1791802 := by
    simpa [prefixWord, tailWord_1791802, baseEnd_1791802] using wordTrace_append hprefix tailTrace_1791802
  have hstable : (prefixWord ++ tailWord_1791802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791802).length < 2 ^ (prefixWord ++ tailWord_1791802).sum := by decide
  have hdescent : baseEnd_1791802 < baseStart_1791802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791811 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1791811 : Nat := 118140960795 + 1791811 * 2 ^ 59
def prefixEnd_1791811 : Nat := 4983230072969 + 3 ^ 40 * 1791811 * 2
def baseEnd_1791811 : Nat := 920060285013394264922117

theorem tailTrace_1791811 : CollatzResearch.WordTrace tailWord_1791811 prefixEnd_1791811 920060285013394264922117 := by
  unfold tailWord_1791811
  simp only [CollatzResearch.WordTrace]
  refine ⟨65352716111582238800655287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43568477407721492533770191 65352716111582238800655287)
  ·
    refine ⟨98029074167373358200982931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65352716111582238800655287 98029074167373358200982931)
    ·
      refine ⟨147043611251060037301474397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98029074167373358200982931 147043611251060037301474397)
      ·
        refine ⟨55141354219147513988052899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147043611251060037301474397 55141354219147513988052899)
        ·
          refine ⟨82712031328721270982079349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55141354219147513988052899 82712031328721270982079349)
          ·
            refine ⟨7754252937067619154569939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82712031328721270982079349 7754252937067619154569939)
            ·
              refine ⟨11631379405601428731854909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754252937067619154569939 11631379405601428731854909)
              ·
                refine ⟨4361767277100535774445591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11631379405601428731854909 4361767277100535774445591)
                ·
                  refine ⟨6542650915650803661668387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361767277100535774445591 6542650915650803661668387)
                  ·
                    refine ⟨9813976373476205492502581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542650915650803661668387 9813976373476205492502581)
                    ·
                      refine ⟨920060285013394264922117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9813976373476205492502581 920060285013394264922117)
                      ·
                        rfl

theorem cell23_1791811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1791811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791811 prefixEnd_1791811 := by exact prefixLift 1791811
  have htrace : WordTrace (prefixWord ++ tailWord_1791811) baseStart_1791811 baseEnd_1791811 := by
    simpa [prefixWord, tailWord_1791811, baseEnd_1791811] using wordTrace_append hprefix tailTrace_1791811
  have hstable : (prefixWord ++ tailWord_1791811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791811).length < 2 ^ (prefixWord ++ tailWord_1791811).sum := by decide
  have hdescent : baseEnd_1791811 < baseStart_1791811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791818 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1791818 : Nat := 118140960795 + 1791818 * 2 ^ 59
def prefixEnd_1791818 : Nat := 4983230072969 + 3 ^ 40 * 1791818 * 2
def baseEnd_1791818 : Nat := 306687959792658579178195

theorem tailTrace_1791818 : CollatzResearch.WordTrace tailWord_1791818 prefixEnd_1791818 306687959792658579178195 := by
  unfold tailWord_1791818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338242855639219749040027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43568647615037919330773405 16338242855639219749040027)
  ·
    refine ⟨24507364283458829623560041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16338242855639219749040027 24507364283458829623560041)
    ·
      refine ⟨18380523212594122217670031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24507364283458829623560041 18380523212594122217670031)
      ·
        refine ⟨27570784818891183326505047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18380523212594122217670031 27570784818891183326505047)
        ·
          refine ⟨41356177228336774989757571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27570784818891183326505047 41356177228336774989757571)
          ·
            refine ⟨62034265842505162484636357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41356177228336774989757571 62034265842505162484636357)
            ·
              refine ⟨11631424845469717965869317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62034265842505162484636357 11631424845469717965869317)
              ·
                refine ⟨2180892158525572118600497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11631424845469717965869317 2180892158525572118600497)
                ·
                  refine ⟨1635669118894179088950373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180892158525572118600497 1635669118894179088950373)
                  ·
                    refine ⟨306687959792658579178195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635669118894179088950373 306687959792658579178195)
                    ·
                      rfl

theorem cell23_1791818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1791818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791818 prefixEnd_1791818 := by exact prefixLift 1791818
  have htrace : WordTrace (prefixWord ++ tailWord_1791818) baseStart_1791818 baseEnd_1791818 := by
    simpa [prefixWord, tailWord_1791818, baseEnd_1791818] using wordTrace_append hprefix tailTrace_1791818
  have hstable : (prefixWord ++ tailWord_1791818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791818).length < 2 ^ (prefixWord ++ tailWord_1791818).sum := by decide
  have hdescent : baseEnd_1791818 < baseStart_1791818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791828 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1791828 : Nat := 118140960795 + 1791828 * 2 ^ 59
def prefixEnd_1791828 : Nat := 4983230072969 + 3 ^ 40 * 1791828 * 2
def baseEnd_1791828 : Nat := 920069014184520698409539

theorem tailTrace_1791828 : CollatzResearch.WordTrace tailWord_1791828 prefixEnd_1791828 920069014184520698409539 := by
  unfold tailWord_1791828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676668076260325352012069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43568890768347100469349425 32676668076260325352012069)
  ·
    refine ⟨6126875264298811003502263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32676668076260325352012069 6126875264298811003502263)
    ·
      refine ⟨9190312896448216505253395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126875264298811003502263 9190312896448216505253395)
      ·
        refine ⟨13785469344672324757880093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190312896448216505253395 13785469344672324757880093)
        ·
          refine ⟨5169551004252121784205035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13785469344672324757880093 5169551004252121784205035)
          ·
            refine ⟨7754326506378182676307553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169551004252121784205035 7754326506378182676307553)
            ·
              refine ⟨5815744879783637007230665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754326506378182676307553 5815744879783637007230665)
              ·
                refine ⟨4361808659837727755422999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815744879783637007230665 4361808659837727755422999)
                ·
                  refine ⟨6542712989756591633134499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361808659837727755422999 6542712989756591633134499)
                  ·
                    refine ⟨9814069484634887449701749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542712989756591633134499 9814069484634887449701749)
                    ·
                      refine ⟨920069014184520698409539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9814069484634887449701749 920069014184520698409539)
                      ·
                        rfl

theorem cell23_1791828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1791828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791828 prefixEnd_1791828 := by exact prefixLift 1791828
  have htrace : WordTrace (prefixWord ++ tailWord_1791828) baseStart_1791828 baseEnd_1791828 := by
    simpa [prefixWord, tailWord_1791828, baseEnd_1791828] using wordTrace_append hprefix tailTrace_1791828
  have hstable : (prefixWord ++ tailWord_1791828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791828).length < 2 ^ (prefixWord ++ tailWord_1791828).sum := by decide
  have hdescent : baseEnd_1791828 < baseStart_1791828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791842 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1791842 : Nat := 118140960795 + 1791842 * 2 ^ 59
def prefixEnd_1791842 : Nat := 4983230072969 + 3 ^ 40 * 1791842 * 2
def baseEnd_1791842 : Nat := 920076202913683643634475

theorem tailTrace_1791842 : CollatzResearch.WordTrace tailWord_1791842 prefixEnd_1791842 920076202913683643634475 := by
  unfold tailWord_1791842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338461693617482773758445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43569231182979954063355853 16338461693617482773758445)
  ·
    refine ⟨6126923135106556040159417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16338461693617482773758445 6126923135106556040159417)
    ·
      refine ⟨4595192351329917030119563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126923135106556040159417 4595192351329917030119563)
      ·
        refine ⟨6892788526994875545179345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595192351329917030119563 6892788526994875545179345)
        ·
          refine ⟨5169591395246156658884509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892788526994875545179345 5169591395246156658884509)
          ·
            refine ⟨1938596773217308747081691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5169591395246156658884509 1938596773217308747081691)
            ·
              refine ⟨2907895159825963120622537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938596773217308747081691 2907895159825963120622537)
              ·
                refine ⟨2180921369869472340466903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907895159825963120622537 2180921369869472340466903)
                ·
                  refine ⟨3271382054804208510700355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180921369869472340466903 3271382054804208510700355)
                  ·
                    refine ⟨4907073082206312766050533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271382054804208510700355 4907073082206312766050533)
                    ·
                      refine ⟨920076202913683643634475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4907073082206312766050533 920076202913683643634475)
                      ·
                        rfl

theorem cell23_1791842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1791842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791842 prefixEnd_1791842 := by exact prefixLift 1791842
  have htrace : WordTrace (prefixWord ++ tailWord_1791842) baseStart_1791842 baseEnd_1791842 := by
    simpa [prefixWord, tailWord_1791842, baseEnd_1791842] using wordTrace_append hprefix tailTrace_1791842
  have hstable : (prefixWord ++ tailWord_1791842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791842).length < 2 ^ (prefixWord ++ tailWord_1791842).sum := by decide
  have hdescent : baseEnd_1791842 < baseStart_1791842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791862 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1791862 : Nat := 118140960795 + 1791862 * 2 ^ 59
def prefixEnd_1791862 : Nat := 4983230072969 + 3 ^ 40 * 1791862 * 2
def baseEnd_1791862 : Nat := 920086472526773565384383

theorem tailTrace_1791862 : CollatzResearch.WordTrace tailWord_1791862 prefixEnd_1791862 920086472526773565384383 := by
  unfold tailWord_1791862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084661014649842156922615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43569717489598316340507893 4084661014649842156922615)
  ·
    refine ⟨6126991521974763235383923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084661014649842156922615 6126991521974763235383923)
    ·
      refine ⟨9190487282962144853075885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126991521974763235383923 9190487282962144853075885)
      ·
        refine ⟨3446432731110804319903457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9190487282962144853075885 3446432731110804319903457)
        ·
          refine ⟨2584824548333103239927593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446432731110804319903457 2584824548333103239927593)
          ·
            refine ⟨1938618411249827429945695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584824548333103239927593 1938618411249827429945695)
            ·
              refine ⟨2907927616874741144918543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938618411249827429945695 2907927616874741144918543)
              ·
                refine ⟨4361891425312111717377815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907927616874741144918543 4361891425312111717377815)
                ·
                  refine ⟨6542837137968167576066723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361891425312111717377815 6542837137968167576066723)
                  ·
                    refine ⟨9814255706952251364100085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542837137968167576066723 9814255706952251364100085)
                    ·
                      refine ⟨920086472526773565384383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9814255706952251364100085 920086472526773565384383)
                      ·
                        rfl

theorem cell23_1791862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1791862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791862 prefixEnd_1791862 := by exact prefixLift 1791862
  have htrace : WordTrace (prefixWord ++ tailWord_1791862) baseStart_1791862 baseEnd_1791862 := by
    simpa [prefixWord, tailWord_1791862, baseEnd_1791862] using wordTrace_append hprefix tailTrace_1791862
  have hstable : (prefixWord ++ tailWord_1791862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791862).length < 2 ^ (prefixWord ++ tailWord_1791862).sum := by decide
  have hdescent : baseEnd_1791862 < baseStart_1791862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791875 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 3]
def baseStart_1791875 : Nat := 118140960795 + 1791875 * 2 ^ 59
def prefixEnd_1791875 : Nat := 4983230072969 + 3 ^ 40 * 1791875 * 2
def baseEnd_1791875 : Nat := 920093147775282014521823

theorem tailTrace_1791875 : CollatzResearch.WordTrace tailWord_1791875 prefixEnd_1791875 920093147775282014521823 := by
  unfold tailWord_1791875
  simp only [CollatzResearch.WordTrace]
  refine ⟨65355050383350377730985079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43570033588900251820656719 65355050383350377730985079)
  ·
    refine ⟨98032575575025566596477619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65355050383350377730985079 98032575575025566596477619)
    ·
      refine ⟨147048863362538349894716429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98032575575025566596477619 147048863362538349894716429)
      ·
        refine ⟨55143323760951881210518661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147048863362538349894716429 55143323760951881210518661)
        ·
          refine ⟨10339373205178477726972249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55143323760951881210518661 10339373205178477726972249)
          ·
            refine ⟨7754529903883858295229187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10339373205178477726972249 7754529903883858295229187)
            ·
              refine ⟨11631794855825787442843781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754529903883858295229187 11631794855825787442843781)
              ·
                refine ⟨2180961535467335145533209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11631794855825787442843781 2180961535467335145533209)
                ·
                  refine ⟨1635721151600501359149907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180961535467335145533209 1635721151600501359149907)
                  ·
                    refine ⟨2453581727400752038724861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635721151600501359149907 2453581727400752038724861)
                    ·
                      refine ⟨920093147775282014521823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453581727400752038724861 920093147775282014521823)
                      ·
                        rfl

theorem cell23_1791875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_1791875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791875 prefixEnd_1791875 := by exact prefixLift 1791875
  have htrace : WordTrace (prefixWord ++ tailWord_1791875) baseStart_1791875 baseEnd_1791875 := by
    simpa [prefixWord, tailWord_1791875, baseEnd_1791875] using wordTrace_append hprefix tailTrace_1791875
  have hstable : (prefixWord ++ tailWord_1791875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791875).length < 2 ^ (prefixWord ++ tailWord_1791875).sum := by decide
  have hdescent : baseEnd_1791875 < baseStart_1791875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791881 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_1791881 : Nat := 118140960795 + 1791881 * 2 ^ 59
def prefixEnd_1791881 : Nat := 4983230072969 + 3 ^ 40 * 1791881 * 2
def baseEnd_1791881 : Nat := 920096228659208991046795

theorem tailTrace_1791881 : CollatzResearch.WordTrace tailWord_1791881 prefixEnd_1791881 920096228659208991046795 := by
  unfold tailWord_1791881
  simp only [CollatzResearch.WordTrace]
  refine ⟨65355269221328640755703497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43570179480885760503802331 65355269221328640755703497)
  ·
    refine ⟨49016451915996480566777623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65355269221328640755703497 49016451915996480566777623)
    ·
      refine ⟨73524677873994720850166435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49016451915996480566777623 73524677873994720850166435)
      ·
        refine ⟨110287016810992081275249653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73524677873994720850166435 110287016810992081275249653)
        ·
          refine ⟨10339407826030507619554655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110287016810992081275249653 10339407826030507619554655)
          ·
            refine ⟨15509111739045761429331983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339407826030507619554655 15509111739045761429331983)
            ·
              refine ⟨23263667608568642143997975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15509111739045761429331983 23263667608568642143997975)
              ·
                refine ⟨34895501412852963215996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23263667608568642143997975 34895501412852963215996963)
                ·
                  refine ⟨52343252119279444823995445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34895501412852963215996963 52343252119279444823995445)
                  ·
                    refine ⟨4907179886182447952249573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52343252119279444823995445 4907179886182447952249573)
                    ·
                      refine ⟨920096228659208991046795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4907179886182447952249573 920096228659208991046795)
                      ·
                        rfl

theorem cell23_1791881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_1791881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791881 prefixEnd_1791881 := by exact prefixLift 1791881
  have htrace : WordTrace (prefixWord ++ tailWord_1791881) baseStart_1791881 baseEnd_1791881 := by
    simpa [prefixWord, tailWord_1791881, baseEnd_1791881] using wordTrace_append hprefix tailTrace_1791881
  have hstable : (prefixWord ++ tailWord_1791881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791881).length < 2 ^ (prefixWord ++ tailWord_1791881).sum := by decide
  have hdescent : baseEnd_1791881 < baseStart_1791881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791892 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1791892 : Nat := 118140960795 + 1791892 * 2 ^ 59
def prefixEnd_1791892 : Nat := 4983230072969 + 3 ^ 40 * 1791892 * 2
def baseEnd_1791892 : Nat := 920101876946408448009245

theorem tailTrace_1791892 : CollatzResearch.WordTrace tailWord_1791892 prefixEnd_1791892 920101876946408448009245 := by
  unfold tailWord_1791892
  simp only [CollatzResearch.WordTrace]
  refine ⟨32677835212144394817176965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43570446949525859756235953 32677835212144394817176965)
  ·
    refine ⟨6127094102277074028220681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32677835212144394817176965 6127094102277074028220681)
    ·
      refine ⟨4595320576707805521165511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6127094102277074028220681 4595320576707805521165511)
      ·
        refine ⟨6892980865061708281748267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595320576707805521165511 6892980865061708281748267)
        ·
          refine ⟨10339471297592562422622401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892980865061708281748267 10339471297592562422622401)
          ·
            refine ⟨7754603473194421816966801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10339471297592562422622401 7754603473194421816966801)
            ·
              refine ⟨5815952604895816362725101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754603473194421816966801 5815952604895816362725101)
              ·
                refine ⟨2180982226835931136021913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5815952604895816362725101 2180982226835931136021913)
                ·
                  refine ⟨1635736670126948352016435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180982226835931136021913 1635736670126948352016435)
                  ·
                    refine ⟨2453605005190422528024653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635736670126948352016435 2453605005190422528024653)
                    ·
                      refine ⟨920101876946408448009245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453605005190422528024653 920101876946408448009245)
                      ·
                        rfl

theorem cell23_1791892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1791892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791892 prefixEnd_1791892 := by exact prefixLift 1791892
  have htrace : WordTrace (prefixWord ++ tailWord_1791892) baseStart_1791892 baseEnd_1791892 := by
    simpa [prefixWord, tailWord_1791892, baseEnd_1791892] using wordTrace_append hprefix tailTrace_1791892
  have hstable : (prefixWord ++ tailWord_1791892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791892).length < 2 ^ (prefixWord ++ tailWord_1791892).sum := by decide
  have hdescent : baseEnd_1791892 < baseStart_1791892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791951 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 7]
def baseStart_1791951 : Nat := 118140960795 + 1791951 * 2 ^ 59
def prefixEnd_1791951 : Nat := 4983230072969 + 3 ^ 40 * 1791951 * 2
def baseEnd_1791951 : Nat := 306710724101674572390491

theorem tailTrace_1791951 : CollatzResearch.WordTrace tailWord_1791951 prefixEnd_1791951 306710724101674572390491 := by
  unfold tailWord_1791951
  simp only [CollatzResearch.WordTrace]
  refine ⟨65357822331075042710751707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43571881554050028473834471 65357822331075042710751707)
  ·
    refine ⟨98036733496612564066127561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65357822331075042710751707 98036733496612564066127561)
    ·
      refine ⟨73527550122459423049595671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98036733496612564066127561 73527550122459423049595671)
      ·
        refine ⟨110291325183689134574393507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73527550122459423049595671 110291325183689134574393507)
        ·
          refine ⟨165436987775533701861590261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110291325183689134574393507 165436987775533701861590261)
          ·
            refine ⟨15509717603956284549524087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165436987775533701861590261 15509717603956284549524087)
            ·
              refine ⟨23264576405934426824286131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15509717603956284549524087 23264576405934426824286131)
              ·
                refine ⟨34896864608901640236429197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23264576405934426824286131 34896864608901640236429197)
                ·
                  refine ⟨13086324228338115088660949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34896864608901640236429197 13086324228338115088660949)
                  ·
                    refine ⟨306710724101674572390491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13086324228338115088660949 306710724101674572390491)
                    ·
                      rfl

theorem cell23_1791951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_1791951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791951 prefixEnd_1791951 := by exact prefixLift 1791951
  have htrace : WordTrace (prefixWord ++ tailWord_1791951) baseStart_1791951 baseEnd_1791951 := by
    simpa [prefixWord, tailWord_1791951, baseEnd_1791951] using wordTrace_append hprefix tailTrace_1791951
  have hstable : (prefixWord ++ tailWord_1791951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791951).length < 2 ^ (prefixWord ++ tailWord_1791951).sum := by decide
  have hdescent : baseEnd_1791951 < baseStart_1791951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791978 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1791978 : Nat := 118140960795 + 1791978 * 2 ^ 59
def prefixEnd_1791978 : Nat := 4983230072969 + 3 ^ 40 * 1791978 * 2
def baseEnd_1791978 : Nat := 920146036282695111533849

theorem tailTrace_1791978 : CollatzResearch.WordTrace tailWord_1791978 prefixEnd_1791978 920146036282695111533849 := by
  unfold tailWord_1791978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339701775494306580496147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43572538067984817547989725 16339701775494306580496147)
  ·
    refine ⟨24509552663241459870744221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16339701775494306580496147 24509552663241459870744221)
    ·
      refine ⟨9191082248715547451529083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24509552663241459870744221 9191082248715547451529083)
      ·
        refine ⟨13786623373073321177293625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191082248715547451529083 13786623373073321177293625)
        ·
          refine ⟨10339967529804990882970219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13786623373073321177293625 10339967529804990882970219)
          ·
            refine ⟨15509951294707486324455329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339967529804990882970219 15509951294707486324455329)
            ·
              refine ⟨11632463471030614743341497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15509951294707486324455329 11632463471030614743341497)
              ·
                refine ⟨8724347603272961057506123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11632463471030614743341497 8724347603272961057506123)
                ·
                  refine ⟨13086521404909441586259185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8724347603272961057506123 13086521404909441586259185)
                  ·
                    refine ⟨9814891053682081189694389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13086521404909441586259185 9814891053682081189694389)
                    ·
                      refine ⟨920146036282695111533849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9814891053682081189694389 920146036282695111533849)
                      ·
                        rfl

theorem cell23_1791978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1791978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791978 prefixEnd_1791978 := by exact prefixLift 1791978
  have htrace : WordTrace (prefixWord ++ tailWord_1791978) baseStart_1791978 baseEnd_1791978 := by
    simpa [prefixWord, tailWord_1791978, baseEnd_1791978] using wordTrace_append hprefix tailTrace_1791978
  have hstable : (prefixWord ++ tailWord_1791978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791978).length < 2 ^ (prefixWord ++ tailWord_1791978).sum := by decide
  have hdescent : baseEnd_1791978 < baseStart_1791978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791985 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_1791985 : Nat := 118140960795 + 1791985 * 2 ^ 59
def prefixEnd_1791985 : Nat := 4983230072969 + 3 ^ 40 * 1791985 * 2
def baseEnd_1791985 : Nat := 306716543549092194715439

theorem tailTrace_1791985 : CollatzResearch.WordTrace tailWord_1791985 prefixEnd_1791985 306716543549092194715439 := by
  unfold tailWord_1791985
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359062412951866517489409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43572708275301244344992939 65359062412951866517489409)
  ·
    refine ⟨49019296809713899888117057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65359062412951866517489409 49019296809713899888117057)
    ·
      refine ⟨36764472607285424916087793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49019296809713899888117057 36764472607285424916087793)
      ·
        refine ⟨27573354455464068687065845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36764472607285424916087793 27573354455464068687065845)
        ·
          refine ⟨2585001980199756439412423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27573354455464068687065845 2585001980199756439412423)
          ·
            refine ⟨3877502970299634659118635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585001980199756439412423 3877502970299634659118635)
            ·
              refine ⟨5816254455449451988677953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877502970299634659118635 5816254455449451988677953)
              ·
                refine ⟨4362190841587088991508465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816254455449451988677953 4362190841587088991508465)
                ·
                  refine ⟨3271643131190316743631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4362190841587088991508465 3271643131190316743631349)
                  ·
                    refine ⟨306716543549092194715439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3271643131190316743631349 306716543549092194715439)
                    ·
                      rfl

theorem cell23_1791985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_1791985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791985 prefixEnd_1791985 := by exact prefixLift 1791985
  have htrace : WordTrace (prefixWord ++ tailWord_1791985) baseStart_1791985 baseEnd_1791985 := by
    simpa [prefixWord, tailWord_1791985, baseEnd_1791985] using wordTrace_append hprefix tailTrace_1791985
  have hstable : (prefixWord ++ tailWord_1791985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791985).length < 2 ^ (prefixWord ++ tailWord_1791985).sum := by decide
  have hdescent : baseEnd_1791985 < baseStart_1791985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792042 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1792042 : Nat := 118140960795 + 1792042 * 2 ^ 59
def prefixEnd_1792042 : Nat := 4983230072969 + 3 ^ 40 * 1792042 * 2
def baseEnd_1792042 : Nat := 920178899044582861133555

theorem tailTrace_1792042 : CollatzResearch.WordTrace tailWord_1792042 prefixEnd_1792042 920178899044582861133555 := by
  unfold tailWord_1792042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340285343436341313078595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43574094249163576834876253 16340285343436341313078595)
  ·
    refine ⟨24510428015154511969617893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16340285343436341313078595 24510428015154511969617893)
    ·
      refine ⟨4595705252841470994303355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24510428015154511969617893 4595705252841470994303355)
      ·
        refine ⟨6893557879262206491455033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595705252841470994303355 6893557879262206491455033)
        ·
          refine ⟨5170168409446654868591275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6893557879262206491455033 5170168409446654868591275)
          ·
            refine ⟨7755252614169982302886913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170168409446654868591275 7755252614169982302886913)
            ·
              refine ⟨5816439460627486727165185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7755252614169982302886913 5816439460627486727165185)
              ·
                refine ⟨4362329595470615045373889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816439460627486727165185 4362329595470615045373889)
                ·
                  refine ⟨3271747196602961284030417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4362329595470615045373889 3271747196602961284030417)
                  ·
                    refine ⟨2453810397452220963022813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271747196602961284030417 2453810397452220963022813)
                    ·
                      refine ⟨920178899044582861133555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453810397452220963022813 920178899044582861133555)
                      ·
                        rfl

theorem cell23_1792042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1792042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792042 prefixEnd_1792042 := by exact prefixLift 1792042
  have htrace : WordTrace (prefixWord ++ tailWord_1792042) baseStart_1792042 baseEnd_1792042 := by
    simpa [prefixWord, tailWord_1792042, baseEnd_1792042] using wordTrace_append hprefix tailTrace_1792042
  have hstable : (prefixWord ++ tailWord_1792042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792042).length < 2 ^ (prefixWord ++ tailWord_1792042).sum := by decide
  have hdescent : baseEnd_1792042 < baseStart_1792042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792049 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 1, 4]
def baseStart_1792049 : Nat := 118140960795 + 1792049 * 2 ^ 59
def prefixEnd_1792049 : Nat := 4983230072969 + 3 ^ 40 * 1792049 * 2
def baseEnd_1792049 : Nat := 306727497803054777915341

theorem tailTrace_1792049 : CollatzResearch.WordTrace tailWord_1792049 prefixEnd_1792049 306727497803054777915341 := by
  unfold tailWord_1792049
  simp only [CollatzResearch.WordTrace]
  refine ⟨65361396684720005447819201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43574264456480003631879467 65361396684720005447819201)
  ·
    refine ⟨49021047513540004085864401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65361396684720005447819201 49021047513540004085864401)
    ·
      refine ⟨36765785635155003064398301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49021047513540004085864401 36765785635155003064398301)
      ·
        refine ⟨13787169613183126149149363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36765785635155003064398301 13787169613183126149149363)
        ·
          refine ⟨20680754419774689223724045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787169613183126149149363 20680754419774689223724045)
          ·
            refine ⟨7755282907415508458896517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20680754419774689223724045 7755282907415508458896517)
            ·
              refine ⟨1454115545140407836043097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7755282907415508458896517 1454115545140407836043097)
              ·
                refine ⟨1090586658855305877032323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454115545140407836043097 1090586658855305877032323)
                ·
                  refine ⟨1635879988282958815548485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090586658855305877032323 1635879988282958815548485)
                  ·
                    refine ⟨306727497803054777915341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635879988282958815548485 306727497803054777915341)
                    ·
                      rfl

theorem cell23_1792049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_1792049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792049 prefixEnd_1792049 := by exact prefixLift 1792049
  have htrace : WordTrace (prefixWord ++ tailWord_1792049) baseStart_1792049 baseEnd_1792049 := by
    simpa [prefixWord, tailWord_1792049, baseEnd_1792049] using wordTrace_append hprefix tailTrace_1792049
  have hstable : (prefixWord ++ tailWord_1792049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792049).length < 2 ^ (prefixWord ++ tailWord_1792049).sum := by decide
  have hdescent : baseEnd_1792049 < baseStart_1792049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792089 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 1, 1, 3]
def baseStart_1792089 : Nat := 118140960795 + 1792089 * 2 ^ 59
def prefixEnd_1792089 : Nat := 4983230072969 + 3 ^ 40 * 1792089 * 2
def baseEnd_1792089 : Nat := 920203032635344177245839

theorem tailTrace_1792089 : CollatzResearch.WordTrace tailWord_1792089 prefixEnd_1792089 920203032635344177245839 := by
  unfold tailWord_1792089
  simp only [CollatzResearch.WordTrace]
  refine ⟨65362855604575092279275321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43575237069716728186183547 65362855604575092279275321)
  ·
    refine ⟨49022141703431319209456491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65362855604575092279275321 49022141703431319209456491)
    ·
      refine ⟨73533212555146978814184737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49022141703431319209456491 73533212555146978814184737)
      ·
        refine ⟨55149909416360234110638553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73533212555146978814184737 55149909416360234110638553)
        ·
          refine ⟨41362432062270175582978915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55149909416360234110638553 41362432062270175582978915)
          ·
            refine ⟨62043648093405263374468373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41362432062270175582978915 62043648093405263374468373)
            ·
              refine ⟨2908296004378371720678205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62043648093405263374468373 2908296004378371720678205)
              ·
                refine ⟨1090611001641889395254327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2908296004378371720678205 1090611001641889395254327)
                ·
                  refine ⟨1635916502462834092881491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090611001641889395254327 1635916502462834092881491)
                  ·
                    refine ⟨2453874753694251139322237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635916502462834092881491 2453874753694251139322237)
                    ·
                      refine ⟨920203032635344177245839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2453874753694251139322237 920203032635344177245839)
                      ·
                        rfl

theorem cell23_1792089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_1792089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792089 prefixEnd_1792089 := by exact prefixLift 1792089
  have htrace : WordTrace (prefixWord ++ tailWord_1792089) baseStart_1792089 baseEnd_1792089 := by
    simpa [prefixWord, tailWord_1792089, baseEnd_1792089] using wordTrace_append hprefix tailTrace_1792089
  have hstable : (prefixWord ++ tailWord_1792089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792089).length < 2 ^ (prefixWord ++ tailWord_1792089).sum := by decide
  have hdescent : baseEnd_1792089 < baseStart_1792089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792092 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1792092 : Nat := 118140960795 + 1792092 * 2 ^ 59
def prefixEnd_1792092 : Nat := 4983230072969 + 3 ^ 40 * 1792092 * 2
def baseEnd_1792092 : Nat := 306734857692435888502775

theorem tailTrace_1792092 : CollatzResearch.WordTrace tailWord_1792092 prefixEnd_1792092 306734857692435888502775 := by
  unfold tailWord_1792092
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681482511782111895817265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43575310015709482527756353 32681482511782111895817265)
  ·
    refine ⟨24511111883836583921862949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32681482511782111895817265 24511111883836583921862949)
    ·
      refine ⟨4595833478219359485349303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24511111883836583921862949 4595833478219359485349303)
      ·
        refine ⟨6893750217329039228023955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595833478219359485349303 6893750217329039228023955)
        ·
          refine ⟨10340625325993558842035933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893750217329039228023955 10340625325993558842035933)
          ·
            refine ⟨3877734497247584565763475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10340625325993558842035933 3877734497247584565763475)
            ·
              refine ⟨5816601745871376848645213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877734497247584565763475 5816601745871376848645213)
              ·
                refine ⟨2181225654701766318241955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5816601745871376848645213 2181225654701766318241955)
                ·
                  refine ⟨3271838482052649477362933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181225654701766318241955 3271838482052649477362933)
                  ·
                    refine ⟨306734857692435888502775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3271838482052649477362933 306734857692435888502775)
                    ·
                      rfl

theorem cell23_1792092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1792092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792092 prefixEnd_1792092 := by exact prefixLift 1792092
  have htrace : WordTrace (prefixWord ++ tailWord_1792092) baseStart_1792092 baseEnd_1792092 := by
    simpa [prefixWord, tailWord_1792092, baseEnd_1792092] using wordTrace_append hprefix tailTrace_1792092
  have hstable : (prefixWord ++ tailWord_1792092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792092).length < 2 ^ (prefixWord ++ tailWord_1792092).sum := by decide
  have hdescent : baseEnd_1792092 < baseStart_1792092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792105 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_1792105 : Nat := 118140960795 + 1792105 * 2 ^ 59
def prefixEnd_1792105 : Nat := 4983230072969 + 3 ^ 40 * 1792105 * 2
def baseEnd_1792105 : Nat := 306737082775272038215255

theorem tailTrace_1792105 : CollatzResearch.WordTrace tailWord_1792105 prefixEnd_1792105 306737082775272038215255 := by
  unfold tailWord_1792105
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363439172517127011857769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43575626115011418007905179 65363439172517127011857769)
  ·
    refine ⟨49022579379387845258893327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65363439172517127011857769 49022579379387845258893327)
    ·
      refine ⟨73533869069081767888339991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49022579379387845258893327 73533869069081767888339991)
      ·
        refine ⟨110300803603622651832509987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73533869069081767888339991 110300803603622651832509987)
        ·
          refine ⟨165451205405433977748764981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110300803603622651832509987 165451205405433977748764981)
          ·
            refine ⟨15511050506759435413946717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165451205405433977748764981 15511050506759435413946717)
            ·
              refine ⟨5816643940034788280230019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15511050506759435413946717 5816643940034788280230019)
              ·
                refine ⟨8724965910052182420345029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816643940034788280230019 8724965910052182420345029)
                ·
                  refine ⟨1635931108134784203814693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8724965910052182420345029 1635931108134784203814693)
                  ·
                    refine ⟨306737082775272038215255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635931108134784203814693 306737082775272038215255)
                    ·
                      rfl

theorem cell23_1792105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_1792105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792105 prefixEnd_1792105 := by exact prefixLift 1792105
  have htrace : WordTrace (prefixWord ++ tailWord_1792105) baseStart_1792105 baseEnd_1792105 := by
    simpa [prefixWord, tailWord_1792105, baseEnd_1792105] using wordTrace_append hprefix tailTrace_1792105
  have hstable : (prefixWord ++ tailWord_1792105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792105).length < 2 ^ (prefixWord ++ tailWord_1792105).sum := by decide
  have hdescent : baseEnd_1792105 < baseStart_1792105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792125 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1792125 : Nat := 118140960795 + 1792125 * 2 ^ 59
def prefixEnd_1792125 : Nat := 4983230072969 + 3 ^ 40 * 1792125 * 2
def baseEnd_1792125 : Nat := 920221517938906036395673

theorem tailTrace_1792125 : CollatzResearch.WordTrace tailWord_1792125 prefixEnd_1792125 920221517938906036395673 := by
  unfold tailWord_1792125
  simp only [CollatzResearch.WordTrace]
  refine ⟨65364168632444670427585829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43576112421629780285057219 65364168632444670427585829)
  ·
    refine ⟨12255781618583375705172343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65364168632444670427585829 12255781618583375705172343)
    ·
      refine ⟨18383672427875063557758515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255781618583375705172343 18383672427875063557758515)
      ·
        refine ⟨27575508641812595336637773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383672427875063557758515 27575508641812595336637773)
        ·
          refine ⟨10340815740679723251239165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27575508641812595336637773 10340815740679723251239165)
          ·
            refine ⟨3877805902754896219214687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10340815740679723251239165 3877805902754896219214687)
            ·
              refine ⟨5816708854132344328822031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877805902754896219214687 5816708854132344328822031)
              ·
                refine ⟨8725063281198516493233047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816708854132344328822031 8725063281198516493233047)
                ·
                  refine ⟨13087594921797774739849571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725063281198516493233047 13087594921797774739849571)
                  ·
                    refine ⟨19631392382696662109774357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13087594921797774739849571 19631392382696662109774357)
                    ·
                      refine ⟨920221517938906036395673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19631392382696662109774357 920221517938906036395673)
                      ·
                        rfl

theorem cell23_1792125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1792125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792125 prefixEnd_1792125 := by exact prefixLift 1792125
  have htrace : WordTrace (prefixWord ++ tailWord_1792125) baseStart_1792125 baseEnd_1792125 := by
    simpa [prefixWord, tailWord_1792125, baseEnd_1792125] using wordTrace_append hprefix tailTrace_1792125
  have hstable : (prefixWord ++ tailWord_1792125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792125).length < 2 ^ (prefixWord ++ tailWord_1792125).sum := by decide
  have hdescent : baseEnd_1792125 < baseStart_1792125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792129 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1792129 : Nat := 118140960795 + 1792129 * 2 ^ 59
def prefixEnd_1792129 : Nat := 4983230072969 + 3 ^ 40 * 1792129 * 2
def baseEnd_1792129 : Nat := 920223571861524020745655

theorem tailTrace_1792129 : CollatzResearch.WordTrace tailWord_1792129 prefixEnd_1792129 920223571861524020745655 := by
  unfold tailWord_1792129
  simp only [CollatzResearch.WordTrace]
  refine ⟨65364314524430179110731441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43576209682953452740487627 65364314524430179110731441)
  ·
    refine ⟨49023235893322634333048581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65364314524430179110731441 49023235893322634333048581)
    ·
      refine ⟨9191856729997993937446609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49023235893322634333048581 9191856729997993937446609)
      ·
        refine ⟨6893892547498495453084957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191856729997993937446609 6893892547498495453084957)
        ·
          refine ⟨2585209705311935794906859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6893892547498495453084957 2585209705311935794906859)
          ·
            refine ⟨3877814557967903692360289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585209705311935794906859 3877814557967903692360289)
            ·
              refine ⟨2908360918475927769270217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877814557967903692360289 2908360918475927769270217)
              ·
                refine ⟨2181270688856945826952663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908360918475927769270217 2181270688856945826952663)
                ·
                  refine ⟨3271906033285418740428995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181270688856945826952663 3271906033285418740428995)
                  ·
                    refine ⟨4907859049928128110643493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271906033285418740428995 4907859049928128110643493)
                    ·
                      refine ⟨920223571861524020745655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4907859049928128110643493 920223571861524020745655)
                      ·
                        rfl

theorem cell23_1792129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1792129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792129 prefixEnd_1792129 := by exact prefixLift 1792129
  have htrace : WordTrace (prefixWord ++ tailWord_1792129) baseStart_1792129 baseEnd_1792129 := by
    simpa [prefixWord, tailWord_1792129, baseEnd_1792129] using wordTrace_append hprefix tailTrace_1792129
  have hstable : (prefixWord ++ tailWord_1792129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792129).length < 2 ^ (prefixWord ++ tailWord_1792129).sum := by decide
  have hdescent : baseEnd_1792129 < baseStart_1792129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792135 : List Nat := [1, 1, 4, 2, 1, 1, 6, 7]
def baseStart_1792135 : Nat := 118140960795 + 1792135 * 2 ^ 59
def prefixEnd_1792135 : Nat := 4983230072969 + 3 ^ 40 * 1792135 * 2
def baseEnd_1792135 : Nat := 34082468620201888787801

theorem tailTrace_1792135 : CollatzResearch.WordTrace tailWord_1792135 prefixEnd_1792135 34082468620201888787801 := by
  unfold tailWord_1792135
  simp only [CollatzResearch.WordTrace]
  refine ⟨65364533362408442135449859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43576355574938961423633239 65364533362408442135449859)
  ·
    refine ⟨98046800043612663203174789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65364533362408442135449859 98046800043612663203174789)
    ·
      refine ⟨18383775008177374350595273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98046800043612663203174789 18383775008177374350595273)
      ·
        refine ⟨13787831256133030762946455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18383775008177374350595273 13787831256133030762946455)
        ·
          refine ⟨20681746884199546144419683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787831256133030762946455 20681746884199546144419683)
          ·
            refine ⟨31022620326299319216629525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20681746884199546144419683 31022620326299319216629525)
            ·
              refine ⟨1454185327795280588279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31022620326299319216629525 1454185327795280588279509)
              ·
                refine ⟨34082468620201888787801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1454185327795280588279509 34082468620201888787801)
                ·
                  rfl

theorem cell23_1792135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 7].length) (baseStart_1792135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792135 prefixEnd_1792135 := by exact prefixLift 1792135
  have htrace : WordTrace (prefixWord ++ tailWord_1792135) baseStart_1792135 baseEnd_1792135 := by
    simpa [prefixWord, tailWord_1792135, baseEnd_1792135] using wordTrace_append hprefix tailTrace_1792135
  have hstable : (prefixWord ++ tailWord_1792135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792135).length < 2 ^ (prefixWord ++ tailWord_1792135).sum := by decide
  have hdescent : baseEnd_1792135 < baseStart_1792135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792152 : List Nat := [2, 1, 2, 4, 4, 1, 9]
def baseStart_1792152 : Nat := 118140960795 + 1792152 * 2 ^ 59
def prefixEnd_1792152 : Nat := 4983230072969 + 3 ^ 40 * 1792152 * 2
def baseEnd_1792152 : Nat := 11360930640945400379729

theorem tailTrace_1792152 : CollatzResearch.WordTrace tailWord_1792152 prefixEnd_1792152 11360930640945400379729 := by
  unfold tailWord_1792152
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682576701673427019409355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43576768935564569359212473 32682576701673427019409355)
  ·
    refine ⟨49023865052510140529114033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32682576701673427019409355 49023865052510140529114033)
    ·
      refine ⟨36767898789382605396835525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49023865052510140529114033 36767898789382605396835525)
      ·
        refine ⟨6893981023009238511906661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36767898789382605396835525 6893981023009238511906661)
        ·
          refine ⟨1292621441814232220982499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6893981023009238511906661 1292621441814232220982499)
          ·
            refine ⟨1938932162721348331473749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292621441814232220982499 1938932162721348331473749)
            ·
              refine ⟨11360930640945400379729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1938932162721348331473749 11360930640945400379729)
              ·
                rfl

theorem cell23_1792152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 9].length) (baseStart_1792152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792152 prefixEnd_1792152 := by exact prefixLift 1792152
  have htrace : WordTrace (prefixWord ++ tailWord_1792152) baseStart_1792152 baseEnd_1792152 := by
    simpa [prefixWord, tailWord_1792152, baseEnd_1792152] using wordTrace_append hprefix tailTrace_1792152
  have hstable : (prefixWord ++ tailWord_1792152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792152).length < 2 ^ (prefixWord ++ tailWord_1792152).sum := by decide
  have hdescent : baseEnd_1792152 < baseStart_1792152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792180 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1792180 : Nat := 118140960795 + 1792180 * 2 ^ 59
def prefixEnd_1792180 : Nat := 4983230072969 + 3 ^ 40 * 1792180 * 2
def baseEnd_1792180 : Nat := 920249759374903321207921

theorem tailTrace_1792180 : CollatzResearch.WordTrace tailWord_1792180 prefixEnd_1792180 920249759374903321207921 := by
  unfold tailWord_1792180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683087323622707410418997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43577449764830276547225329 32683087323622707410418997)
  ·
    refine ⟨3064039436589628819726781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32683087323622707410418997 3064039436589628819726781)
    ·
      refine ⟨1149014788721110807397543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3064039436589628819726781 1149014788721110807397543)
      ·
        refine ⟨1723522183081666211096315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149014788721110807397543 1723522183081666211096315)
        ·
          refine ⟨2585283274622499316644473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723522183081666211096315 2585283274622499316644473)
          ·
            refine ⟨1938962455966874487483355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585283274622499316644473 1938962455966874487483355)
            ·
              refine ⟨2908443683950311731225033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938962455966874487483355 2908443683950311731225033)
              ·
                refine ⟨2181332762962733798418775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908443683950311731225033 2181332762962733798418775)
                ·
                  refine ⟨3271999144444100697628163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181332762962733798418775 3271999144444100697628163)
                  ·
                    refine ⟨4907998716666151046442245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271999144444100697628163 4907998716666151046442245)
                    ·
                      refine ⟨920249759374903321207921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4907998716666151046442245 920249759374903321207921)
                      ·
                        rfl

theorem cell23_1792180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1792180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792180 prefixEnd_1792180 := by exact prefixLift 1792180
  have htrace : WordTrace (prefixWord ++ tailWord_1792180) baseStart_1792180 baseEnd_1792180 := by
    simpa [prefixWord, tailWord_1792180, baseEnd_1792180] using wordTrace_append hprefix tailTrace_1792180
  have hstable : (prefixWord ++ tailWord_1792180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792180).length < 2 ^ (prefixWord ++ tailWord_1792180).sum := by decide
  have hdescent : baseEnd_1792180 < baseStart_1792180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792215 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1792215 : Nat := 118140960795 + 1792215 * 2 ^ 59
def prefixEnd_1792215 : Nat := 4983230072969 + 3 ^ 40 * 1792215 * 2
def baseEnd_1792215 : Nat := 920267731197810684270259

theorem tailTrace_1792215 : CollatzResearch.WordTrace tailWord_1792215 prefixEnd_1792215 920267731197810684270259 := by
  unfold tailWord_1792215
  simp only [CollatzResearch.WordTrace]
  refine ⟨65367451202118615798362099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43578300801412410532241399 65367451202118615798362099)
  ·
    refine ⟨98051176803177923697543149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65367451202118615798362099 98051176803177923697543149)
    ·
      refine ⟨36769191301191721386578681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98051176803177923697543149 36769191301191721386578681)
      ·
        refine ⟨27576893475893791039934011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36769191301191721386578681 27576893475893791039934011)
        ·
          refine ⟨41365340213840686559901017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27576893475893791039934011 41365340213840686559901017)
          ·
            refine ⟨31024005160380514919925763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41365340213840686559901017 31024005160380514919925763)
            ·
              refine ⟨46536007740570772379888645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31024005160380514919925763 46536007740570772379888645)
              ·
                refine ⟨8725501451357019821229121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46536007740570772379888645 8725501451357019821229121)
                ·
                  refine ⟨6544126088517764865921841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725501451357019821229121 6544126088517764865921841)
                  ·
                    refine ⟨4908094566388323649441381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544126088517764865921841 4908094566388323649441381)
                    ·
                      refine ⟨920267731197810684270259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4908094566388323649441381 920267731197810684270259)
                      ·
                        rfl

theorem cell23_1792215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1792215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792215 prefixEnd_1792215 := by exact prefixLift 1792215
  have htrace : WordTrace (prefixWord ++ tailWord_1792215) baseStart_1792215 baseEnd_1792215 := by
    simpa [prefixWord, tailWord_1792215, baseEnd_1792215] using wordTrace_append hprefix tailTrace_1792215
  have hstable : (prefixWord ++ tailWord_1792215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792215).length < 2 ^ (prefixWord ++ tailWord_1792215).sum := by decide
  have hdescent : baseEnd_1792215 < baseStart_1792215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792219 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 2, 2, 2]
def baseStart_1792219 : Nat := 118140960795 + 1792219 * 2 ^ 59
def prefixEnd_1792219 : Nat := 4983230072969 + 3 ^ 40 * 1792219 * 2
def baseEnd_1792219 : Nat := 920269785120428668620241

theorem tailTrace_1792219 : CollatzResearch.WordTrace tailWord_1792219 prefixEnd_1792219 920269785120428668620241 := by
  unfold tailWord_1792219
  simp only [CollatzResearch.WordTrace]
  refine ⟨65367597094104124481507711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43578398062736082987671807 65367597094104124481507711)
  ·
    refine ⟨98051395641156186722261567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65367597094104124481507711 98051395641156186722261567)
    ·
      refine ⟨147077093461734280083392351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98051395641156186722261567 147077093461734280083392351)
      ·
        refine ⟨220615640192601420125088527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147077093461734280083392351 220615640192601420125088527)
        ·
          refine ⟨330923460288902130187632791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220615640192601420125088527 330923460288902130187632791)
          ·
            refine ⟨496385190433353195281449187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330923460288902130187632791 496385190433353195281449187)
            ·
              refine ⟨744577785650029792922173781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496385190433353195281449187 744577785650029792922173781)
              ·
                refine ⟨2181380231396571658951681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 744577785650029792922173781 2181380231396571658951681)
                ·
                  refine ⟨1636035173547428744213761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181380231396571658951681 1636035173547428744213761)
                  ·
                    refine ⟨1227026380160571558160321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1636035173547428744213761 1227026380160571558160321)
                    ·
                      refine ⟨920269785120428668620241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227026380160571558160321 920269785120428668620241)
                      ·
                        rfl

theorem cell23_1792219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2, 2].length) (baseStart_1792219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792219 prefixEnd_1792219 := by exact prefixLift 1792219
  have htrace : WordTrace (prefixWord ++ tailWord_1792219) baseStart_1792219 baseEnd_1792219 := by
    simpa [prefixWord, tailWord_1792219, baseEnd_1792219] using wordTrace_append hprefix tailTrace_1792219
  have hstable : (prefixWord ++ tailWord_1792219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792219).length < 2 ^ (prefixWord ++ tailWord_1792219).sum := by decide
  have hdescent : baseEnd_1792219 < baseStart_1792219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792225 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 7]
def baseStart_1792225 : Nat := 118140960795 + 1792225 * 2 ^ 59
def prefixEnd_1792225 : Nat := 4983230072969 + 3 ^ 40 * 1792225 * 2
def baseEnd_1792225 : Nat := 102252540667150627238357

theorem tailTrace_1792225 : CollatzResearch.WordTrace tailWord_1792225 prefixEnd_1792225 102252540667150627238357 := by
  unfold tailWord_1792225
  simp only [CollatzResearch.WordTrace]
  refine ⟨65367815932082387506226129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43578543954721591670817419 65367815932082387506226129)
  ·
    refine ⟨49025861949061790629669597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65367815932082387506226129 49025861949061790629669597)
    ·
      refine ⟨18384698230898171486126099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49025861949061790629669597 18384698230898171486126099)
      ·
        refine ⟨27577047346347257229189149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18384698230898171486126099 27577047346347257229189149)
        ·
          refine ⟨10341392754880221460945931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27577047346347257229189149 10341392754880221460945931)
          ·
            refine ⟨15512089132320332191418897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341392754880221460945931 15512089132320332191418897)
            ·
              refine ⟨11634066849240249143564173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15512089132320332191418897 11634066849240249143564173)
              ·
                refine ⟨4362775068465093428836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11634066849240249143564173 4362775068465093428836565)
                ·
                  refine ⟨102252540667150627238357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4362775068465093428836565 102252540667150627238357)
                  ·
                    rfl

theorem cell23_1792225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_1792225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792225 prefixEnd_1792225 := by exact prefixLift 1792225
  have htrace : WordTrace (prefixWord ++ tailWord_1792225) baseStart_1792225 baseEnd_1792225 := by
    simpa [prefixWord, tailWord_1792225, baseEnd_1792225] using wordTrace_append hprefix tailTrace_1792225
  have hstable : (prefixWord ++ tailWord_1792225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792225).length < 2 ^ (prefixWord ++ tailWord_1792225).sum := by decide
  have hdescent : baseEnd_1792225 < baseStart_1792225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792232 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1792232 : Nat := 118140960795 + 1792232 * 2 ^ 59
def prefixEnd_1792232 : Nat := 4983230072969 + 3 ^ 40 * 1792232 * 2
def baseEnd_1792232 : Nat := 920276460368937117757681

theorem tailTrace_1792232 : CollatzResearch.WordTrace tailWord_1792232 prefixEnd_1792232 920276460368937117757681 := by
  unfold tailWord_1792232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32684035621528513850865475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43578714162038018467820633 32684035621528513850865475)
  ·
    refine ⟨49026053432292770776298213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32684035621528513850865475 49026053432292770776298213)
    ·
      refine ⟨9192385018554894520555915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49026053432292770776298213 9192385018554894520555915)
      ·
        refine ⟨13788577527832341780833873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9192385018554894520555915 13788577527832341780833873)
        ·
          refine ⟨10341433145874256335625405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13788577527832341780833873 10341433145874256335625405)
          ·
            refine ⟨3878037429702846125859527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10341433145874256335625405 3878037429702846125859527)
            ·
              refine ⟨5817056144554269188789291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878037429702846125859527 5817056144554269188789291)
              ·
                refine ⟨8725584216831403783183937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817056144554269188789291 8725584216831403783183937)
                ·
                  refine ⟨6544188162623552837387953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725584216831403783183937 6544188162623552837387953)
                  ·
                    refine ⟨4908141121967664628040965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544188162623552837387953 4908141121967664628040965)
                    ·
                      refine ⟨920276460368937117757681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4908141121967664628040965 920276460368937117757681)
                      ·
                        rfl

theorem cell23_1792232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1792232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792232 prefixEnd_1792232 := by exact prefixLift 1792232
  have htrace : WordTrace (prefixWord ++ tailWord_1792232) baseStart_1792232 baseEnd_1792232 := by
    simpa [prefixWord, tailWord_1792232, baseEnd_1792232] using wordTrace_append hprefix tailTrace_1792232
  have hstable : (prefixWord ++ tailWord_1792232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792232).length < 2 ^ (prefixWord ++ tailWord_1792232).sum := by decide
  have hdescent : baseEnd_1792232 < baseStart_1792232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792242 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1792242 : Nat := 118140960795 + 1792242 * 2 ^ 59
def prefixEnd_1792242 : Nat := 4983230072969 + 3 ^ 40 * 1792242 * 2
def baseEnd_1792242 : Nat := 102253510575053564292515

theorem tailTrace_1792242 : CollatzResearch.WordTrace tailWord_1792242 prefixEnd_1792242 102253510575053564292515 := by
  unfold tailWord_1792242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342108993255199852398745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43578957315347199606396653 16342108993255199852398745)
  ·
    refine ⟨12256581744941399889299059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16342108993255199852398745 12256581744941399889299059)
    ·
      refine ⟨18384872617412099833948589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256581744941399889299059 18384872617412099833948589)
      ·
        refine ⟨6894327231529537437730721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18384872617412099833948589 6894327231529537437730721)
        ·
          refine ⟨5170745423647153078298041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6894327231529537437730721 5170745423647153078298041)
          ·
            refine ⟨3878059067735364808723531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170745423647153078298041 3878059067735364808723531)
            ·
              refine ⟨5817088601603047213085297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878059067735364808723531 5817088601603047213085297)
              ·
                refine ⟨4362816451202285409813973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5817088601603047213085297 4362816451202285409813973)
                ·
                  refine ⟨102253510575053564292515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4362816451202285409813973 102253510575053564292515)
                  ·
                    rfl

theorem cell23_1792242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1792242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792242 prefixEnd_1792242 := by exact prefixLift 1792242
  have htrace : WordTrace (prefixWord ++ tailWord_1792242) baseStart_1792242 baseEnd_1792242 := by
    simpa [prefixWord, tailWord_1792242, baseEnd_1792242] using wordTrace_append hprefix tailTrace_1792242
  have hstable : (prefixWord ++ tailWord_1792242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792242).length < 2 ^ (prefixWord ++ tailWord_1792242).sum := by decide
  have hdescent : baseEnd_1792242 < baseStart_1792242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792255 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 7]
def baseStart_1792255 : Nat := 118140960795 + 1792255 * 2 ^ 59
def prefixEnd_1792255 : Nat := 4983230072969 + 3 ^ 40 * 1792255 * 2
def baseEnd_1792255 : Nat := 306762756807996842590025

theorem tailTrace_1792255 : CollatzResearch.WordTrace tailWord_1792255 prefixEnd_1792255 306762756807996842590025 := by
  unfold tailWord_1792255
  simp only [CollatzResearch.WordTrace]
  refine ⟨65368910121973702629818219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43579273414649135086545479 65368910121973702629818219)
  ·
    refine ⟨98053365182960553944727329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65368910121973702629818219 98053365182960553944727329)
    ·
      refine ⟨73540023887220415458545497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98053365182960553944727329 73540023887220415458545497)
      ·
        refine ⟨55155017915415311593909123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73540023887220415458545497 55155017915415311593909123)
        ·
          refine ⟨82732526873122967390863685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55155017915415311593909123 82732526873122967390863685)
          ·
            refine ⟨15512348788710556385786941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82732526873122967390863685 15512348788710556385786941)
            ·
              refine ⟨5817130795766458644670103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15512348788710556385786941 5817130795766458644670103)
              ·
                refine ⟨8725696193649687967005155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817130795766458644670103 8725696193649687967005155)
                ·
                  refine ⟨13088544290474531950507733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725696193649687967005155 13088544290474531950507733)
                  ·
                    refine ⟨306762756807996842590025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13088544290474531950507733 306762756807996842590025)
                    ·
                      rfl

theorem cell23_1792255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_1792255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792255 prefixEnd_1792255 := by exact prefixLift 1792255
  have htrace : WordTrace (prefixWord ++ tailWord_1792255) baseStart_1792255 baseEnd_1792255 := by
    simpa [prefixWord, tailWord_1792255, baseEnd_1792255] using wordTrace_append hprefix tailTrace_1792255
  have hstable : (prefixWord ++ tailWord_1792255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792255).length < 2 ^ (prefixWord ++ tailWord_1792255).sum := by decide
  have hdescent : baseEnd_1792255 < baseStart_1792255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792286 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1792286 : Nat := 118140960795 + 1792286 * 2 ^ 59
def prefixEnd_1792286 : Nat := 4983230072969 + 3 ^ 40 * 1792286 * 2
def baseEnd_1792286 : Nat := 920304188324279906482433

theorem tailTrace_1792286 : CollatzResearch.WordTrace tailWord_1792286 prefixEnd_1792286 920304188324279906482433 := by
  unfold tailWord_1792286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171255098107674365524589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43580027189907596616131141 8171255098107674365524589)
  ·
    refine ⟨3064220661790377887071721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8171255098107674365524589 3064220661790377887071721)
    ·
      refine ⟨2298165496342783415303791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064220661790377887071721 2298165496342783415303791)
      ·
        refine ⟨3447248244514175122955687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298165496342783415303791 3447248244514175122955687)
        ·
          refine ⟨5170872366771262684433531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447248244514175122955687 5170872366771262684433531)
          ·
            refine ⟨7756308550156894026650297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170872366771262684433531 7756308550156894026650297)
            ·
              refine ⟨5817231412617670519987723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756308550156894026650297 5817231412617670519987723)
              ·
                refine ⟨8725847118926505779981585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817231412617670519987723 8725847118926505779981585)
                ·
                  refine ⟨6544385339194879334986189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725847118926505779981585 6544385339194879334986189)
                  ·
                    refine ⟨2454144502198079750619821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6544385339194879334986189 2454144502198079750619821)
                    ·
                      refine ⟨920304188324279906482433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454144502198079750619821 920304188324279906482433)
                      ·
                        rfl

theorem cell23_1792286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1792286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792286 prefixEnd_1792286 := by exact prefixLift 1792286
  have htrace : WordTrace (prefixWord ++ tailWord_1792286) baseStart_1792286 baseEnd_1792286 := by
    simpa [prefixWord, tailWord_1792286, baseEnd_1792286] using wordTrace_append hprefix tailTrace_1792286
  have hstable : (prefixWord ++ tailWord_1792286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792286).length < 2 ^ (prefixWord ++ tailWord_1792286).sum := by decide
  have hdescent : baseEnd_1792286 < baseStart_1792286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792292 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1792292 : Nat := 118140960795 + 1792292 * 2 ^ 59
def prefixEnd_1792292 : Nat := 4983230072969 + 3 ^ 40 * 1792292 * 2
def baseEnd_1792292 : Nat := 920307269208206883007405

theorem tailTrace_1792292 : CollatzResearch.WordTrace tailWord_1792292 prefixEnd_1792292 920307269208206883007405 := by
  unfold tailWord_1792292
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685129811419828974457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43580173081893105299276753 32685129811419828974457565)
  ·
    refine ⟨12256923679282435865421587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32685129811419828974457565 12256923679282435865421587)
    ·
      refine ⟨18385385518923653798132381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256923679282435865421587 18385385518923653798132381)
      ·
        refine ⟨6894519569596370174299643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18385385518923653798132381 6894519569596370174299643)
        ·
          refine ⟨10341779354394555261449465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894519569596370174299643 10341779354394555261449465)
          ·
            refine ⟨7756334515795916446087099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341779354394555261449465 7756334515795916446087099)
            ·
              refine ⟨11634501773693874669130649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756334515795916446087099 11634501773693874669130649)
              ·
                refine ⟨8725876330270406001847987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11634501773693874669130649 8725876330270406001847987)
                ·
                  refine ⟨13088814495405609002771981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725876330270406001847987 13088814495405609002771981)
                  ·
                    refine ⟨4908305435777103376039493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13088814495405609002771981 4908305435777103376039493)
                    ·
                      refine ⟨920307269208206883007405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4908305435777103376039493 920307269208206883007405)
                      ·
                        rfl

theorem cell23_1792292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1792292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792292 prefixEnd_1792292 := by exact prefixLift 1792292
  have htrace : WordTrace (prefixWord ++ tailWord_1792292) baseStart_1792292 baseEnd_1792292 := by
    simpa [prefixWord, tailWord_1792292, baseEnd_1792292] using wordTrace_append hprefix tailTrace_1792292
  have hstable : (prefixWord ++ tailWord_1792292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792292).length < 2 ^ (prefixWord ++ tailWord_1792292).sum := by decide
  have hdescent : baseEnd_1792292 < baseStart_1792292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792312 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_1792312 : Nat := 118140960795 + 1792312 * 2 ^ 59
def prefixEnd_1792312 : Nat := 4983230072969 + 3 ^ 40 * 1792312 * 2
def baseEnd_1792312 : Nat := 920317538821296804757313

theorem tailTrace_1792312 : CollatzResearch.WordTrace tailWord_1792312 prefixEnd_1792312 920317538821296804757313 := by
  unfold tailWord_1792312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685494541383600682321595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43580659388511467576428793 32685494541383600682321595)
  ·
    refine ⟨49028241812075401023482393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32685494541383600682321595 49028241812075401023482393)
    ·
      refine ⟨36771181359056550767611795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49028241812075401023482393 36771181359056550767611795)
      ·
        refine ⟨55156772038584826151417693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36771181359056550767611795 55156772038584826151417693)
        ·
          refine ⟨20683789514469309806781635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55156772038584826151417693 20683789514469309806781635)
          ·
            refine ⟨31025684271703964710172453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20683789514469309806781635 31025684271703964710172453)
            ·
              refine ⟨5817315800944493383157335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31025684271703964710172453 5817315800944493383157335)
              ·
                refine ⟨8725973701416740074736003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817315800944493383157335 8725973701416740074736003)
                ·
                  refine ⟨13088960552125110112104005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725973701416740074736003 13088960552125110112104005)
                  ·
                    refine ⟨2454180103523458146019501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13088960552125110112104005 2454180103523458146019501)
                    ·
                      refine ⟨920317538821296804757313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454180103523458146019501 920317538821296804757313)
                      ·
                        rfl

theorem cell23_1792312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_1792312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792312 prefixEnd_1792312 := by exact prefixLift 1792312
  have htrace : WordTrace (prefixWord ++ tailWord_1792312) baseStart_1792312 baseEnd_1792312 := by
    simpa [prefixWord, tailWord_1792312, baseEnd_1792312] using wordTrace_append hprefix tailTrace_1792312
  have hstable : (prefixWord ++ tailWord_1792312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792312).length < 2 ^ (prefixWord ++ tailWord_1792312).sum := by decide
  have hdescent : baseEnd_1792312 < baseStart_1792312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792332 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 6]
def baseStart_1792332 : Nat := 118140960795 + 1792332 * 2 ^ 59
def prefixEnd_1792332 : Nat := 4983230072969 + 3 ^ 40 * 1792332 * 2
def baseEnd_1792332 : Nat := 102258645381598525167469

theorem tailTrace_1792332 : CollatzResearch.WordTrace tailWord_1792332 prefixEnd_1792332 102258645381598525167469 := by
  unfold tailWord_1792332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685859271347372390185625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43581145695129829853580833 32685859271347372390185625)
  ·
    refine ⟨24514394453510529292639219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32685859271347372390185625 24514394453510529292639219)
    ·
      refine ⟨36771591680265793938958829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24514394453510529292639219 36771591680265793938958829)
      ·
        refine ⟨13789346880099672727109561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36771591680265793938958829 13789346880099672727109561)
        ·
          refine ⟨10342010160074754545332171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13789346880099672727109561 10342010160074754545332171)
          ·
            refine ⟨15513015240112131817998257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342010160074754545332171 15513015240112131817998257)
            ·
              refine ⟨11634761430084098863498693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15513015240112131817998257 11634761430084098863498693)
              ·
                refine ⟨2181517768140768536906005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11634761430084098863498693 2181517768140768536906005)
                ·
                  refine ⟨102258645381598525167469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2181517768140768536906005 102258645381598525167469)
                  ·
                    rfl

theorem cell23_1792332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_1792332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792332 prefixEnd_1792332 := by exact prefixLift 1792332
  have htrace : WordTrace (prefixWord ++ tailWord_1792332) baseStart_1792332 baseEnd_1792332 := by
    simpa [prefixWord, tailWord_1792332, baseEnd_1792332] using wordTrace_append hprefix tailTrace_1792332
  have hstable : (prefixWord ++ tailWord_1792332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792332).length < 2 ^ (prefixWord ++ tailWord_1792332).sum := by decide
  have hdescent : baseEnd_1792332 < baseStart_1792332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_1792335 : Nat := 118140960795 + 1792335 * 2 ^ 59
def prefixEnd_1792335 : Nat := 4983230072969 + 3 ^ 40 * 1792335 * 2
def baseEnd_1792335 : Nat := 920329348876350214769707

theorem tailTrace_1792335 : CollatzResearch.WordTrace tailWord_1792335 prefixEnd_1792335 920329348876350214769707 := by
  unfold tailWord_1792335
  simp only [CollatzResearch.WordTrace]
  refine ⟨65371827961683876292730459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43581218641122584195153639 65371827961683876292730459)
  ·
    refine ⟨98057741942525814439095689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65371827961683876292730459 98057741942525814439095689)
    ·
      refine ⟨73543306456894360829321767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98057741942525814439095689 73543306456894360829321767)
      ·
        refine ⟨110314959685341541243982651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73543306456894360829321767 110314959685341541243982651)
        ·
          refine ⟨165472439528012311865973977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110314959685341541243982651 165472439528012311865973977)
          ·
            refine ⟨124104329646009233899480483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165472439528012311865973977 124104329646009233899480483)
            ·
              refine ⟨186156494469013850849220725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124104329646009233899480483 186156494469013850849220725)
              ·
                refine ⟨17452171356470048517114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186156494469013850849220725 17452171356470048517114443)
                ·
                  refine ⟨26178257034705072775671665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452171356470048517114443 26178257034705072775671665)
                  ·
                    refine ⟨19633692776028804581753749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26178257034705072775671665 19633692776028804581753749)
                    ·
                      refine ⟨920329348876350214769707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19633692776028804581753749 920329348876350214769707)
                      ·
                        rfl

theorem cell23_1792335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_1792335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792335 prefixEnd_1792335 := by exact prefixLift 1792335
  have htrace : WordTrace (prefixWord ++ tailWord_1792335) baseStart_1792335 baseEnd_1792335 := by
    simpa [prefixWord, tailWord_1792335, baseEnd_1792335] using wordTrace_append hprefix tailTrace_1792335
  have hstable : (prefixWord ++ tailWord_1792335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792335).length < 2 ^ (prefixWord ++ tailWord_1792335).sum := by decide
  have hdescent : baseEnd_1792335 < baseStart_1792335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792345 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_1792345 : Nat := 118140960795 + 1792345 * 2 ^ 59
def prefixEnd_1792345 : Nat := 4983230072969 + 3 ^ 40 * 1792345 * 2
def baseEnd_1792345 : Nat := 306778161227631725214887

theorem tailTrace_1792345 : CollatzResearch.WordTrace tailWord_1792345 prefixEnd_1792345 306778161227631725214887 := by
  unfold tailWord_1792345
  simp only [CollatzResearch.WordTrace]
  refine ⟨65372192691647648000594489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43581461794431765333729659 65372192691647648000594489)
  ·
    refine ⟨49029144518735736000445867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65372192691647648000594489 49029144518735736000445867)
    ·
      refine ⟨73543716778103604000668801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49029144518735736000445867 73543716778103604000668801)
      ·
        refine ⟨55157787583577703000501601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73543716778103604000668801 55157787583577703000501601)
        ·
          refine ⟨41368340687683277250376201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55157787583577703000501601 41368340687683277250376201)
          ·
            refine ⟨31026255515762457937782151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41368340687683277250376201 31026255515762457937782151)
            ·
              refine ⟨46539383273643686906673227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31026255515762457937782151 46539383273643686906673227)
              ·
                refine ⟨69809074910465530360009841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46539383273643686906673227 69809074910465530360009841)
                ·
                  refine ⟨52356806182849147770007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69809074910465530360009841 52356806182849147770007381)
                  ·
                    refine ⟨306778161227631725214887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 52356806182849147770007381 306778161227631725214887)
                    ·
                      rfl

theorem cell23_1792345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_1792345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792345 prefixEnd_1792345 := by exact prefixLift 1792345
  have htrace : WordTrace (prefixWord ++ tailWord_1792345) baseStart_1792345 baseEnd_1792345 := by
    simpa [prefixWord, tailWord_1792345, baseEnd_1792345] using wordTrace_append hprefix tailTrace_1792345
  have hstable : (prefixWord ++ tailWord_1792345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792345).length < 2 ^ (prefixWord ++ tailWord_1792345).sum := by decide
  have hdescent : baseEnd_1792345 < baseStart_1792345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792392 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1792392 : Nat := 118140960795 + 1792392 * 2 ^ 59
def prefixEnd_1792392 : Nat := 4983230072969 + 3 ^ 40 * 1792392 * 2
def baseEnd_1792392 : Nat := 306786205757885497252315

theorem tailTrace_1792392 : CollatzResearch.WordTrace tailWord_1792392 prefixEnd_1792392 306786205757885497252315 := by
  unfold tailWord_1792392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32686953461238687513777715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43582604614984916685036953 32686953461238687513777715)
  ·
    refine ⟨49030430191858031270666573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32686953461238687513777715 49030430191858031270666573)
    ·
      refine ⟨18386411321946761726499965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49030430191858031270666573 18386411321946761726499965)
      ·
        refine ⟨6894904245730035647437487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18386411321946761726499965 6894904245730035647437487)
        ·
          refine ⟨10342356368595053471156231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894904245730035647437487 10342356368595053471156231)
          ·
            refine ⟨15513534552892580206734347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342356368595053471156231 15513534552892580206734347)
            ·
              refine ⟨23270301829338870310101521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513534552892580206734347 23270301829338870310101521)
              ·
                refine ⟨17452726372004152732576141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23270301829338870310101521 17452726372004152732576141)
                ·
                  refine ⟨6544772389501557274716053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17452726372004152732576141 6544772389501557274716053)
                  ·
                    refine ⟨306786205757885497252315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6544772389501557274716053 306786205757885497252315)
                    ·
                      rfl

theorem cell23_1792392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1792392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792392 prefixEnd_1792392 := by exact prefixLift 1792392
  have htrace : WordTrace (prefixWord ++ tailWord_1792392) baseStart_1792392 baseEnd_1792392 := by
    simpa [prefixWord, tailWord_1792392, baseEnd_1792392] using wordTrace_append hprefix tailTrace_1792392
  have hstable : (prefixWord ++ tailWord_1792392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792392).length < 2 ^ (prefixWord ++ tailWord_1792392).sum := by decide
  have hdescent : baseEnd_1792392 < baseStart_1792392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792393 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 1, 1, 3]
def baseStart_1792393 : Nat := 118140960795 + 1792393 * 2 ^ 59
def prefixEnd_1792393 : Nat := 4983230072969 + 3 ^ 40 * 1792393 * 2
def baseEnd_1792393 : Nat := 920359130754310987844441

theorem tailTrace_1792393 : CollatzResearch.WordTrace tailWord_1792393 prefixEnd_1792393 920359130754310987844441 := by
  unfold tailWord_1792393
  simp only [CollatzResearch.WordTrace]
  refine ⟨65373943395473752198341833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43582628930315834798894555 65373943395473752198341833)
  ·
    refine ⟨49030457546605314148756375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65373943395473752198341833 49030457546605314148756375)
    ·
      refine ⟨73545686319907971223134563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49030457546605314148756375 73545686319907971223134563)
      ·
        refine ⟨110318529479861956834701845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73545686319907971223134563 110318529479861956834701845)
        ·
          refine ⟨5171181069368529226626649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110318529479861956834701845 5171181069368529226626649)
          ·
            refine ⟨3878385802026396919969987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5171181069368529226626649 3878385802026396919969987)
            ·
              refine ⟨5817578703039595379954981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878385802026396919969987 5817578703039595379954981)
              ·
                refine ⟨1090796006819924133741559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5817578703039595379954981 1090796006819924133741559)
                ·
                  refine ⟨1636194010229886200612339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090796006819924133741559 1636194010229886200612339)
                  ·
                    refine ⟨2454291015344829300918509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1636194010229886200612339 2454291015344829300918509)
                    ·
                      refine ⟨920359130754310987844441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454291015344829300918509 920359130754310987844441)
                      ·
                        rfl

theorem cell23_1792393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 1, 3].length) (baseStart_1792393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792393 prefixEnd_1792393 := by exact prefixLift 1792393
  have htrace : WordTrace (prefixWord ++ tailWord_1792393) baseStart_1792393 baseEnd_1792393 := by
    simpa [prefixWord, tailWord_1792393, baseEnd_1792393] using wordTrace_append hprefix tailTrace_1792393
  have hstable : (prefixWord ++ tailWord_1792393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792393).length < 2 ^ (prefixWord ++ tailWord_1792393).sum := by decide
  have hdescent : baseEnd_1792393 < baseStart_1792393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792409 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_1792409 : Nat := 118140960795 + 1792409 * 2 ^ 59
def prefixEnd_1792409 : Nat := 4983230072969 + 3 ^ 40 * 1792409 * 2
def baseEnd_1792409 : Nat := 306789115481594308414789

theorem tailTrace_1792409 : CollatzResearch.WordTrace tailWord_1792409 prefixEnd_1792409 306789115481594308414789 := by
  unfold tailWord_1792409
  simp only [CollatzResearch.WordTrace]
  refine ⟨65374526963415786930924281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43583017975610524620616187 65374526963415786930924281)
  ·
    refine ⟨49030895222561840198193211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65374526963415786930924281 49030895222561840198193211)
    ·
      refine ⟨73546342833842760297289817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49030895222561840198193211 73546342833842760297289817)
      ·
        refine ⟨55159757125382070222967363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73546342833842760297289817 55159757125382070222967363)
        ·
          refine ⟨82739635688073105334451045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55159757125382070222967363 82739635688073105334451045)
          ·
            refine ⟨15513681691513707250209571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82739635688073105334451045 15513681691513707250209571)
            ·
              refine ⟨23270522537270560875314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513681691513707250209571 23270522537270560875314357)
              ·
                refine ⟨2181611487869115082060721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23270522537270560875314357 2181611487869115082060721)
                ·
                  refine ⟨1636208615901836311545541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181611487869115082060721 1636208615901836311545541)
                  ·
                    refine ⟨306789115481594308414789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636208615901836311545541 306789115481594308414789)
                    ·
                      rfl

theorem cell23_1792409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_1792409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792409 prefixEnd_1792409 := by exact prefixLift 1792409
  have htrace : WordTrace (prefixWord ++ tailWord_1792409) baseStart_1792409 baseEnd_1792409 := by
    simpa [prefixWord, tailWord_1792409, baseEnd_1792409] using wordTrace_append hprefix tailTrace_1792409
  have hstable : (prefixWord ++ tailWord_1792409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792409).length < 2 ^ (prefixWord ++ tailWord_1792409).sum := by decide
  have hdescent : baseEnd_1792409 < baseStart_1792409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792416 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2]
def baseStart_1792416 : Nat := 118140960795 + 1792416 * 2 ^ 59
def prefixEnd_1792416 : Nat := 4983230072969 + 3 ^ 40 * 1792416 * 2
def baseEnd_1792416 : Nat := 920370940809364397856835

theorem tailTrace_1792416 : CollatzResearch.WordTrace tailWord_1792416 prefixEnd_1792416 920370940809364397856835 := by
  unfold tailWord_1792416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32687391137195213563214551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43583188182926951417619401 32687391137195213563214551)
  ·
    refine ⟨49031086705792820344821827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32687391137195213563214551 49031086705792820344821827)
    ·
      refine ⟨73546630058689230517232741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49031086705792820344821827 73546630058689230517232741)
      ·
        refine ⟨13789993136004230721981139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73546630058689230517232741 13789993136004230721981139)
        ·
          refine ⟨20684989704006346082971709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789993136004230721981139 20684989704006346082971709)
          ·
            refine ⟨7756871139002379781114391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20684989704006346082971709 7756871139002379781114391)
            ·
              refine ⟨11635306708503569671671587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756871139002379781114391 11635306708503569671671587)
              ·
                refine ⟨17452960062755354507507381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635306708503569671671587 17452960062755354507507381)
                ·
                  refine ⟨1636215005883314485078817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17452960062755354507507381 1636215005883314485078817)
                  ·
                    refine ⟨1227161254412485863809113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1636215005883314485078817 1227161254412485863809113)
                    ·
                      refine ⟨920370940809364397856835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227161254412485863809113 920370940809364397856835)
                      ·
                        rfl

theorem cell23_1792416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_1792416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792416 prefixEnd_1792416 := by exact prefixLift 1792416
  have htrace : WordTrace (prefixWord ++ tailWord_1792416) baseStart_1792416 baseEnd_1792416 := by
    simpa [prefixWord, tailWord_1792416, baseEnd_1792416] using wordTrace_append hprefix tailTrace_1792416
  have hstable : (prefixWord ++ tailWord_1792416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792416).length < 2 ^ (prefixWord ++ tailWord_1792416).sum := by decide
  have hdescent : baseEnd_1792416 < baseStart_1792416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792419 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1792419 : Nat := 118140960795 + 1792419 * 2 ^ 59
def prefixEnd_1792419 : Nat := 4983230072969 + 3 ^ 40 * 1792419 * 2
def baseEnd_1792419 : Nat := 920372481251327886119321

theorem tailTrace_1792419 : CollatzResearch.WordTrace tailWord_1792419 prefixEnd_1792419 920372481251327886119321 := by
  unfold tailWord_1792419
  simp only [CollatzResearch.WordTrace]
  refine ⟨65374891693379558638788311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43583261128919705759192207 65374891693379558638788311)
  ·
    refine ⟨98062337540069337958182467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65374891693379558638788311 98062337540069337958182467)
    ·
      refine ⟨147093506310104006937273701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98062337540069337958182467 147093506310104006937273701)
      ·
        refine ⟨27580032433144501300738819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147093506310104006937273701 27580032433144501300738819)
        ·
          refine ⟨41370048649716751951108229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27580032433144501300738819 41370048649716751951108229)
          ·
            refine ⟨7756884121821890990832793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41370048649716751951108229 7756884121821890990832793)
            ·
              refine ⟨5817663091366418243124595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756884121821890990832793 5817663091366418243124595)
              ·
                refine ⟨8726494637049627364686893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817663091366418243124595 8726494637049627364686893)
                ·
                  refine ⟨3272435488893610261757585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8726494637049627364686893 3272435488893610261757585)
                  ·
                    refine ⟨2454326616670207696318189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3272435488893610261757585 2454326616670207696318189)
                    ·
                      refine ⟨920372481251327886119321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454326616670207696318189 920372481251327886119321)
                      ·
                        rfl

theorem cell23_1792419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1792419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792419 prefixEnd_1792419 := by exact prefixLift 1792419
  have htrace : WordTrace (prefixWord ++ tailWord_1792419) baseStart_1792419 baseEnd_1792419 := by
    simpa [prefixWord, tailWord_1792419, baseEnd_1792419] using wordTrace_append hprefix tailTrace_1792419
  have hstable : (prefixWord ++ tailWord_1792419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792419).length < 2 ^ (prefixWord ++ tailWord_1792419).sum := by decide
  have hdescent : baseEnd_1792419 < baseStart_1792419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
