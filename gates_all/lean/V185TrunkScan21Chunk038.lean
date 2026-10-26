import V185TrunkScan21Chunk037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_459431 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 4]
def baseStart_459431 : Nat := 118140960795 + 459431 * 2 ^ 59
def prefixEnd_459431 : Nat := 4983230072969 + 3 ^ 40 * 459431 * 2
def baseEnd_459431 : Nat := 104848413589287647910943

theorem tailTrace_459431 : CollatzResearch.WordTrace tailWord_459431 prefixEnd_459431 104848413589287647910943 := by
  unfold tailWord_459431
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756825198567426413026147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11171216799044950942017431 16756825198567426413026147)
  ·
    refine ⟨25135237797851139619539221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16756825198567426413026147 25135237797851139619539221)
    ·
      refine ⟨1178214271774272169665901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25135237797851139619539221 1178214271774272169665901)
      ·
        refine ⟨441830351915352063624713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1178214271774272169665901 441830351915352063624713)
        ·
          refine ⟨331372763936514047718535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441830351915352063624713 331372763936514047718535)
          ·
            refine ⟨497059145904771071577803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331372763936514047718535 497059145904771071577803)
            ·
              refine ⟨745588718857156607366705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497059145904771071577803 745588718857156607366705)
              ·
                refine ⟨559191539142867455525029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745588718857156607366705 559191539142867455525029)
                ·
                  refine ⟨104848413589287647910943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559191539142867455525029 104848413589287647910943)
                  ·
                    rfl

theorem cell21_459431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].length) (baseStart_459431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459431 prefixEnd_459431 := by exact prefixLift 459431
  have htrace : WordTrace (prefixWord ++ tailWord_459431) baseStart_459431 baseEnd_459431 := by
    simpa [prefixWord, tailWord_459431, baseEnd_459431] using wordTrace_append hprefix tailTrace_459431
  have hstable : (prefixWord ++ tailWord_459431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459431).length < 2 ^ (prefixWord ++ tailWord_459431).sum := by decide
  have hdescent : baseEnd_459431 < baseStart_459431 := by decide
  rcases family_descends (prefixWord ++ tailWord_459431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459439 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_459439 : Nat := 118140960795 + 459439 * 2 ^ 59
def prefixEnd_459439 : Nat := 4983230072969 + 3 ^ 40 * 459439 * 2
def baseEnd_459439 : Nat := 104850239298281411777593

theorem tailTrace_459439 : CollatzResearch.WordTrace tailWord_459439 prefixEnd_459439 104850239298281411777593 := by
  unfold tailWord_459439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757116982538443779317371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11171411321692295852878247 16757116982538443779317371)
  ·
    refine ⟨25135675473807665668976057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16757116982538443779317371 25135675473807665668976057)
    ·
      refine ⟨18851756605355749251732043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25135675473807665668976057 18851756605355749251732043)
      ·
        refine ⟨28277634908033623877598065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851756605355749251732043 28277634908033623877598065)
        ·
          refine ⟨21208226181025217908198549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28277634908033623877598065 21208226181025217908198549)
          ·
            refine ⟨994135602235557089446807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21208226181025217908198549 994135602235557089446807)
            ·
              refine ⟨1491203403353335634170211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994135602235557089446807 1491203403353335634170211)
              ·
                refine ⟨2236805105030003451255317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491203403353335634170211 2236805105030003451255317)
                ·
                  refine ⟨104850239298281411777593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236805105030003451255317 104850239298281411777593)
                  ·
                    rfl

theorem cell21_459439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_459439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459439 prefixEnd_459439 := by exact prefixLift 459439
  have htrace : WordTrace (prefixWord ++ tailWord_459439) baseStart_459439 baseEnd_459439 := by
    simpa [prefixWord, tailWord_459439, baseEnd_459439] using wordTrace_append hprefix tailTrace_459439
  have hstable : (prefixWord ++ tailWord_459439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459439).length < 2 ^ (prefixWord ++ tailWord_459439).sum := by decide
  have hdescent : baseEnd_459439 < baseStart_459439 := by decide
  rcases family_descends (prefixWord ++ tailWord_459439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459462 : List Nat := [6, 1, 2, 1, 2, 2, 2, 5]
def baseStart_459462 : Nat := 118140960795 + 459462 * 2 ^ 59
def prefixEnd_459462 : Nat := 4983230072969 + 3 ^ 40 * 459462 * 2
def baseEnd_459462 : Nat := 34951829403879494298071

theorem tailTrace_459462 : CollatzResearch.WordTrace tailWord_459462 prefixEnd_459462 34951829403879494298071 := by
  unfold tailWord_459462
  simp only [CollatzResearch.WordTrace]
  refine ⟨523686120670472459606395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11171970574303412471603093 523686120670472459606395)
  ·
    refine ⟨785529181005708689409593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523686120670472459606395 785529181005708689409593)
    ·
      refine ⟨589146885754281517057195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 785529181005708689409593 589146885754281517057195)
      ·
        refine ⟨883720328631422275585793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589146885754281517057195 883720328631422275585793)
        ·
          refine ⟨662790246473566706689345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883720328631422275585793 662790246473566706689345)
          ·
            refine ⟨497092684855175030017009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662790246473566706689345 497092684855175030017009)
            ·
              refine ⟨372819513641381272512757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497092684855175030017009 372819513641381272512757)
              ·
                refine ⟨34951829403879494298071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372819513641381272512757 34951829403879494298071)
                ·
                  rfl

theorem cell21_459462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_459462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459462 prefixEnd_459462 := by exact prefixLift 459462
  have htrace : WordTrace (prefixWord ++ tailWord_459462) baseStart_459462 baseEnd_459462 := by
    simpa [prefixWord, tailWord_459462, baseEnd_459462] using wordTrace_append hprefix tailTrace_459462
  have hstable : (prefixWord ++ tailWord_459462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459462).length < 2 ^ (prefixWord ++ tailWord_459462).sum := by decide
  have hdescent : baseEnd_459462 < baseStart_459462 := by decide
  rcases family_descends (prefixWord ++ tailWord_459462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459470 : List Nat := [4, 1, 1, 1, 3, 3, 1, 7]
def baseStart_459470 : Nat := 118140960795 + 459470 * 2 ^ 59
def prefixEnd_459470 : Nat := 4983230072969 + 3 ^ 40 * 459470 * 2
def baseEnd_459470 : Nat := 34952437973544082253621

theorem tailTrace_459470 : CollatzResearch.WordTrace tailWord_459470 prefixEnd_459470 34952437973544082253621 := by
  unfold tailWord_459470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094780955678267009211983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11172165096950757382463909 2094780955678267009211983)
  ·
    refine ⟨3142171433517400513817975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2094780955678267009211983 3142171433517400513817975)
    ·
      refine ⟨4713257150276100770726963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142171433517400513817975 4713257150276100770726963)
      ·
        refine ⟨7069885725414151156090445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713257150276100770726963 7069885725414151156090445)
        ·
          refine ⟨2651207147030306683533917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7069885725414151156090445 2651207147030306683533917)
          ·
            refine ⟨994202680136365006325219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651207147030306683533917 994202680136365006325219)
            ·
              refine ⟨1491304020204547509487829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994202680136365006325219 1491304020204547509487829)
              ·
                refine ⟨34952437973544082253621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1491304020204547509487829 34952437973544082253621)
                ·
                  rfl

theorem cell21_459470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_459470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459470 prefixEnd_459470 := by exact prefixLift 459470
  have htrace : WordTrace (prefixWord ++ tailWord_459470) baseStart_459470 baseEnd_459470 := by
    simpa [prefixWord, tailWord_459470, baseEnd_459470] using wordTrace_append hprefix tailTrace_459470
  have hstable : (prefixWord ++ tailWord_459470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459470).length < 2 ^ (prefixWord ++ tailWord_459470).sum := by decide
  have hdescent : baseEnd_459470 < baseStart_459470 := by decide
  rcases family_descends (prefixWord ++ tailWord_459470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459476 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_459476 : Nat := 118140960795 + 459476 * 2 ^ 59
def prefixEnd_459476 : Nat := 4983230072969 + 3 ^ 40 * 459476 * 2
def baseEnd_459476 : Nat := 104858683202377569660851

theorem tailTrace_459476 : CollatzResearch.WordTrace tailWord_459476 prefixEnd_459476 104858683202377569660851 := by
  unfold tailWord_459476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379233241702199549207141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11172310988936266065609521 8379233241702199549207141)
  ·
    refine ⟨1571106232819162415476339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8379233241702199549207141 1571106232819162415476339)
    ·
      refine ⟨2356659349228743623214509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571106232819162415476339 2356659349228743623214509)
      ·
        refine ⟨883747255960778858705441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2356659349228743623214509 883747255960778858705441)
        ·
          refine ⟨662810441970584144029081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883747255960778858705441 662810441970584144029081)
          ·
            refine ⟨497107831477938108021811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662810441970584144029081 497107831477938108021811)
            ·
              refine ⟨745661747216907162032717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497107831477938108021811 745661747216907162032717)
              ·
                refine ⟨279623155206340185762269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745661747216907162032717 279623155206340185762269)
                ·
                  refine ⟨104858683202377569660851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279623155206340185762269 104858683202377569660851)
                  ·
                    rfl

theorem cell21_459476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_459476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459476 prefixEnd_459476 := by exact prefixLift 459476
  have htrace : WordTrace (prefixWord ++ tailWord_459476) baseStart_459476 baseEnd_459476 := by
    simpa [prefixWord, tailWord_459476, baseEnd_459476] using wordTrace_append hprefix tailTrace_459476
  have hstable : (prefixWord ++ tailWord_459476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459476).length < 2 ^ (prefixWord ++ tailWord_459476).sum := by decide
  have hdescent : baseEnd_459476 < baseStart_459476 := by decide
  rcases family_descends (prefixWord ++ tailWord_459476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459529 : List Nat := [1, 2, 1, 1, 3, 2, 4, 7]
def baseStart_459529 : Nat := 118140960795 + 459529 * 2 ^ 59
def prefixEnd_459529 : Nat := 4983230072969 + 3 ^ 40 * 459529 * 2
def baseEnd_459529 : Nat := 34956926174820418425803

theorem tailTrace_459529 : CollatzResearch.WordTrace tailWord_459529 prefixEnd_459529 34956926174820418425803 := by
  unfold tailWord_459529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760399552212389150093641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173599701474926100062427 16760399552212389150093641)
  ·
    refine ⟨12570299664159291862570231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16760399552212389150093641 12570299664159291862570231)
    ·
      refine ⟨18855449496238937793855347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12570299664159291862570231 18855449496238937793855347)
      ·
        refine ⟨28283174244358406690783021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18855449496238937793855347 28283174244358406690783021)
        ·
          refine ⟨10606190341634402509043633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28283174244358406690783021 10606190341634402509043633)
          ·
            refine ⟨7954642756225801881782725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10606190341634402509043633 7954642756225801881782725)
            ·
              refine ⟨1491495516792337852834261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7954642756225801881782725 1491495516792337852834261)
              ·
                refine ⟨34956926174820418425803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1491495516792337852834261 34956926174820418425803)
                ·
                  rfl

theorem cell21_459529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_459529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459529 prefixEnd_459529 := by exact prefixLift 459529
  have htrace : WordTrace (prefixWord ++ tailWord_459529) baseStart_459529 baseEnd_459529 := by
    simpa [prefixWord, tailWord_459529, baseEnd_459529] using wordTrace_append hprefix tailTrace_459529
  have hstable : (prefixWord ++ tailWord_459529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459529).length < 2 ^ (prefixWord ++ tailWord_459529).sum := by decide
  have hdescent : baseEnd_459529 < baseStart_459529 := by decide
  rcases family_descends (prefixWord ++ tailWord_459529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459605 : List Nat := [1, 3, 2, 2, 2, 1, 10]
def baseStart_459605 : Nat := 118140960795 + 459605 * 2 ^ 59
def prefixEnd_459605 : Nat := 4983230072969 + 3 ^ 40 * 459605 * 2
def baseEnd_459605 : Nat := 11654235862211334667843

theorem tailTrace_459605 : CollatzResearch.WordTrace tailWord_459605 prefixEnd_459605 11654235862211334667843 := by
  unfold tailWord_459605
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763171499937054129860269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11175447666624702753240179 16763171499937054129860269)
  ·
    refine ⟨6286189312476395298697601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16763171499937054129860269 6286189312476395298697601)
    ·
      refine ⟨4714641984357296474023201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6286189312476395298697601 4714641984357296474023201)
      ·
        refine ⟨3535981488267972355517401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4714641984357296474023201 3535981488267972355517401)
        ·
          refine ⟨2651986116200979266638051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535981488267972355517401 2651986116200979266638051)
          ·
            refine ⟨3977979174301468899957077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651986116200979266638051 3977979174301468899957077)
            ·
              refine ⟨11654235862211334667843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3977979174301468899957077 11654235862211334667843)
              ·
                rfl

theorem cell21_459605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 10].length) (baseStart_459605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459605 prefixEnd_459605 := by exact prefixLift 459605
  have htrace : WordTrace (prefixWord ++ tailWord_459605) baseStart_459605 baseEnd_459605 := by
    simpa [prefixWord, tailWord_459605, baseEnd_459605] using wordTrace_append hprefix tailTrace_459605
  have hstable : (prefixWord ++ tailWord_459605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459605).length < 2 ^ (prefixWord ++ tailWord_459605).sum := by decide
  have hdescent : baseEnd_459605 < baseStart_459605 := by decide
  rcases family_descends (prefixWord ++ tailWord_459605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459729 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 3]
def baseStart_459729 : Nat := 118140960795 + 459729 * 2 ^ 59
def prefixEnd_459729 : Nat := 4983230072969 + 3 ^ 40 * 459729 * 2
def baseEnd_459729 : Nat := 104916421249305351943667

theorem tailTrace_459729 : CollatzResearch.WordTrace tailWord_459729 prefixEnd_459729 104916421249305351943667 := by
  unfold tailWord_459729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767694151487823307374241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178462767658548871582827 16767694151487823307374241)
  ·
    refine ⟨12575770613615867480530681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16767694151487823307374241 12575770613615867480530681)
    ·
      refine ⟨9431827960211900610398011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12575770613615867480530681 9431827960211900610398011)
      ·
        refine ⟨14147741940317850915597017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431827960211900610398011 14147741940317850915597017)
        ·
          refine ⟨10610806455238388186697763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14147741940317850915597017 10610806455238388186697763)
          ·
            refine ⟨15916209682857582280046645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610806455238388186697763 15916209682857582280046645)
            ·
              refine ⟨1492144657767898338754373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15916209682857582280046645 1492144657767898338754373)
              ·
                refine ⟨279777123331480938516445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1492144657767898338754373 279777123331480938516445)
                ·
                  refine ⟨104916421249305351943667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279777123331480938516445 104916421249305351943667)
                  ·
                    rfl

theorem cell21_459729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_459729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459729 prefixEnd_459729 := by exact prefixLift 459729
  have htrace : WordTrace (prefixWord ++ tailWord_459729) baseStart_459729 baseEnd_459729 := by
    simpa [prefixWord, tailWord_459729, baseEnd_459729] using wordTrace_append hprefix tailTrace_459729
  have hstable : (prefixWord ++ tailWord_459729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459729).length < 2 ^ (prefixWord ++ tailWord_459729).sum := by decide
  have hdescent : baseEnd_459729 < baseStart_459729 := by decide
  rcases family_descends (prefixWord ++ tailWord_459729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459746 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_459746 : Nat := 118140960795 + 459746 * 2 ^ 59
def prefixEnd_459746 : Nat := 4983230072969 + 3 ^ 40 * 459746 * 2
def baseEnd_459746 : Nat := 104920300880917100160299

theorem tailTrace_459746 : CollatzResearch.WordTrace tailWord_459746 prefixEnd_459746 104920300880917100160299 := by
  unfold tailWord_459746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192078548106558802685773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11178876128284156807162061 4192078548106558802685773)
  ·
    refine ⟨1572029455539959551007165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4192078548106558802685773 1572029455539959551007165)
    ·
      refine ⟨589511045827484831627687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1572029455539959551007165 589511045827484831627687)
      ·
        refine ⟨884266568741227247441531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589511045827484831627687 884266568741227247441531)
        ·
          refine ⟨1326399853111840871162297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884266568741227247441531 1326399853111840871162297)
          ·
            refine ⟨994799889833880653371723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326399853111840871162297 994799889833880653371723)
            ·
              refine ⟨1492199834750820980057585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994799889833880653371723 1492199834750820980057585)
              ·
                refine ⟨1119149876063115735043189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492199834750820980057585 1119149876063115735043189)
                ·
                  refine ⟨104920300880917100160299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119149876063115735043189 104920300880917100160299)
                  ·
                    rfl

theorem cell21_459746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_459746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459746 prefixEnd_459746 := by exact prefixLift 459746
  have htrace : WordTrace (prefixWord ++ tailWord_459746) baseStart_459746 baseEnd_459746 := by
    simpa [prefixWord, tailWord_459746, baseEnd_459746] using wordTrace_append hprefix tailTrace_459746
  have hstable : (prefixWord ++ tailWord_459746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459746).length < 2 ^ (prefixWord ++ tailWord_459746).sum := by decide
  have hdescent : baseEnd_459746 < baseStart_459746 := by decide
  rcases family_descends (prefixWord ++ tailWord_459746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459771 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_459771 : Nat := 118140960795 + 459771 * 2 ^ 59
def prefixEnd_459771 : Nat := 4983230072969 + 3 ^ 40 * 459771 * 2
def baseEnd_459771 : Nat := 104926006221522612243581

theorem tailTrace_459771 : CollatzResearch.WordTrace tailWord_459771 prefixEnd_459771 104926006221522612243581 := by
  unfold tailWord_459771
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769226017335664480403167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11179484011557109653602111 16769226017335664480403167)
  ·
    refine ⟨25153839026003496720604751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16769226017335664480403167 25153839026003496720604751)
    ·
      refine ⟨37730758539005245080907127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25153839026003496720604751 37730758539005245080907127)
      ·
        refine ⟨56596137808507867621360691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37730758539005245080907127 56596137808507867621360691)
        ·
          refine ⟨84894206712761801432041037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56596137808507867621360691 84894206712761801432041037)
          ·
            refine ⟨31835327517285675537015389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84894206712761801432041037 31835327517285675537015389)
            ·
              refine ⟨11938247818982128326380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31835327517285675537015389 11938247818982128326380771)
              ·
                refine ⟨17907371728473192489571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938247818982128326380771 17907371728473192489571157)
                ·
                  refine ⟨104926006221522612243581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17907371728473192489571157 104926006221522612243581)
                  ·
                    rfl

theorem cell21_459771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_459771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459771 prefixEnd_459771 := by exact prefixLift 459771
  have htrace : WordTrace (prefixWord ++ tailWord_459771) baseStart_459771 baseEnd_459771 := by
    simpa [prefixWord, tailWord_459771, baseEnd_459771] using wordTrace_append hprefix tailTrace_459771
  have hstable : (prefixWord ++ tailWord_459771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459771).length < 2 ^ (prefixWord ++ tailWord_459771).sum := by decide
  have hdescent : baseEnd_459771 < baseStart_459771 := by decide
  rcases family_descends (prefixWord ++ tailWord_459771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459788 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_459788 : Nat := 118140960795 + 459788 * 2 ^ 59
def prefixEnd_459788 : Nat := 4983230072969 + 3 ^ 40 * 459788 * 2
def baseEnd_459788 : Nat := 104929885853134360460213

theorem tailTrace_459788 : CollatzResearch.WordTrace tailWord_459788 prefixEnd_459788 104929885853134360460213 := by
  unfold tailWord_459788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384923029137038191886009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11179897372182717589181345 8384923029137038191886009)
  ·
    refine ⟨6288692271852778643914507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8384923029137038191886009 6288692271852778643914507)
    ·
      refine ⟨9433038407779167965871761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288692271852778643914507 9433038407779167965871761)
      ·
        refine ⟨7074778805834375974403821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433038407779167965871761 7074778805834375974403821)
        ·
          refine ⟨2653042052187890990401433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7074778805834375974403821 2653042052187890990401433)
          ·
            refine ⟨1989781539140918242801075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653042052187890990401433 1989781539140918242801075)
            ·
              refine ⟨2984672308711377364201613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989781539140918242801075 2984672308711377364201613)
              ·
                refine ⟨1119252115766766511575605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984672308711377364201613 1119252115766766511575605)
                ·
                  refine ⟨104929885853134360460213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119252115766766511575605 104929885853134360460213)
                  ·
                    rfl

theorem cell21_459788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_459788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459788 prefixEnd_459788 := by exact prefixLift 459788
  have htrace : WordTrace (prefixWord ++ tailWord_459788) baseStart_459788 baseEnd_459788 := by
    simpa [prefixWord, tailWord_459788, baseEnd_459788] using wordTrace_append hprefix tailTrace_459788
  have hstable : (prefixWord ++ tailWord_459788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459788).length < 2 ^ (prefixWord ++ tailWord_459788).sum := by decide
  have hdescent : baseEnd_459788 < baseStart_459788 := by decide
  rcases family_descends (prefixWord ++ tailWord_459788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459808 : List Nat := [2, 1, 1, 7, 1, 2, 2, 5]
def baseStart_459808 : Nat := 118140960795 + 459808 * 2 ^ 59
def prefixEnd_459808 : Nat := 4983230072969 + 3 ^ 40 * 459808 * 2
def baseEnd_459808 : Nat := 34978150041872923375613

theorem tailTrace_459808 : CollatzResearch.WordTrace tailWord_459808 prefixEnd_459808 34978150041872923375613 := by
  unfold tailWord_459808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385287759100809899750039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11180383678801079866333385 8385287759100809899750039)
  ·
    refine ⟨12577931638651214849625059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8385287759100809899750039 12577931638651214849625059)
    ·
      refine ⟨18866897457976822274437589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577931638651214849625059 18866897457976822274437589)
      ·
        refine ⟨442192909171331772057131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18866897457976822274437589 442192909171331772057131)
        ·
          refine ⟨663289363756997658085697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442192909171331772057131 663289363756997658085697)
          ·
            refine ⟨497467022817748243564273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663289363756997658085697 497467022817748243564273)
            ·
              refine ⟨373100267113311182673205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497467022817748243564273 373100267113311182673205)
              ·
                refine ⟨34978150041872923375613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373100267113311182673205 34978150041872923375613)
                ·
                  rfl

theorem cell21_459808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_459808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459808 prefixEnd_459808 := by exact prefixLift 459808
  have htrace : WordTrace (prefixWord ++ tailWord_459808) baseStart_459808 baseEnd_459808 := by
    simpa [prefixWord, tailWord_459808, baseEnd_459808] using wordTrace_append hprefix tailTrace_459808
  have hstable : (prefixWord ++ tailWord_459808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459808).length < 2 ^ (prefixWord ++ tailWord_459808).sum := by decide
  have hdescent : baseEnd_459808 < baseStart_459808 := by decide
  rcases family_descends (prefixWord ++ tailWord_459808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459833 : List Nat := [1, 2, 1, 5, 2, 1, 9]
def baseStart_459833 : Nat := 118140960795 + 459833 * 2 ^ 59
def prefixEnd_459833 : Nat := 4983230072969 + 3 ^ 40 * 459833 * 2
def baseEnd_459833 : Nat := 11660017274024920245569

theorem tailTrace_459833 : CollatzResearch.WordTrace tailWord_459833 prefixEnd_459833 11660017274024920245569 := by
  unfold tailWord_459833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771487343111049069160153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11180991562074032712773435 16771487343111049069160153)
  ·
    refine ⟨12578615507333286801870115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16771487343111049069160153 12578615507333286801870115)
    ·
      refine ⟨18867923260999930202805173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12578615507333286801870115 18867923260999930202805173)
      ·
        refine ⟨1768867805718743456512985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18867923260999930202805173 1768867805718743456512985)
        ·
          refine ⟨1326650854289057592384739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768867805718743456512985 1326650854289057592384739)
          ·
            refine ⟨1989976281433586388577109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326650854289057592384739 1989976281433586388577109)
            ·
              refine ⟨11660017274024920245569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1989976281433586388577109 11660017274024920245569)
              ·
                rfl

theorem cell21_459833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 9].length) (baseStart_459833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459833 prefixEnd_459833 := by exact prefixLift 459833
  have htrace : WordTrace (prefixWord ++ tailWord_459833) baseStart_459833 baseEnd_459833 := by
    simpa [prefixWord, tailWord_459833, baseEnd_459833] using wordTrace_append hprefix tailTrace_459833
  have hstable : (prefixWord ++ tailWord_459833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459833).length < 2 ^ (prefixWord ++ tailWord_459833).sum := by decide
  have hdescent : baseEnd_459833 < baseStart_459833 := by decide
  rcases family_descends (prefixWord ++ tailWord_459833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459853 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 4]
def baseStart_459853 : Nat := 118140960795 + 459853 * 2 ^ 59
def prefixEnd_459853 : Nat := 4983230072969 + 3 ^ 40 * 459853 * 2
def baseEnd_459853 : Nat := 104944719738708691876747

theorem tailTrace_459853 : CollatzResearch.WordTrace tailWord_459853 prefixEnd_459853 104944719738708691876747 := by
  unfold tailWord_459853
  simp only [CollatzResearch.WordTrace]
  refine ⟨16772216803038592484888213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11181477868692394989925475 16772216803038592484888213)
  ·
    refine ⟨786197662642434022729135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16772216803038592484888213 786197662642434022729135)
    ·
      refine ⟨1179296493963651034093703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786197662642434022729135 1179296493963651034093703)
      ·
        refine ⟨1768944740945476551140555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179296493963651034093703 1768944740945476551140555)
        ·
          refine ⟨2653417111418214826710833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768944740945476551140555 2653417111418214826710833)
          ·
            refine ⟨1990062833563661120033125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653417111418214826710833 1990062833563661120033125)
            ·
              refine ⟨373136781293186460006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1990062833563661120033125 373136781293186460006211)
              ·
                refine ⟨559705171939779690009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373136781293186460006211 559705171939779690009317)
                ·
                  refine ⟨104944719738708691876747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559705171939779690009317 104944719738708691876747)
                  ·
                    rfl

theorem cell21_459853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_459853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459853 prefixEnd_459853 := by exact prefixLift 459853
  have htrace : WordTrace (prefixWord ++ tailWord_459853) baseStart_459853 baseEnd_459853 := by
    simpa [prefixWord, tailWord_459853, baseEnd_459853] using wordTrace_append hprefix tailTrace_459853
  have hstable : (prefixWord ++ tailWord_459853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459853).length < 2 ^ (prefixWord ++ tailWord_459853).sum := by decide
  have hdescent : baseEnd_459853 < baseStart_459853 := by decide
  rcases family_descends (prefixWord ++ tailWord_459853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459895 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_459895 : Nat := 118140960795 + 459895 * 2 ^ 59
def prefixEnd_459895 : Nat := 4983230072969 + 3 ^ 40 * 459895 * 2
def baseEnd_459895 : Nat := 104954304710925952176661

theorem tailTrace_459895 : CollatzResearch.WordTrace tailWord_459895 prefixEnd_459895 104954304710925952176661 := by
  unfold tailWord_459895
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773748668886433657917139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11182499112590955771944759 16773748668886433657917139)
  ·
    refine ⟨25160623003329650486875709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16773748668886433657917139 25160623003329650486875709)
    ·
      refine ⟨9435233626248618932578391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25160623003329650486875709 9435233626248618932578391)
      ·
        refine ⟨14152850439372928398867587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435233626248618932578391 14152850439372928398867587)
        ·
          refine ⟨21229275659059392598301381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152850439372928398867587 21229275659059392598301381)
          ·
            refine ⟨3980489186073636112181509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21229275659059392598301381 3980489186073636112181509)
            ·
              refine ⟨746341722388806771034033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3980489186073636112181509 746341722388806771034033)
              ·
                refine ⟨559756291791605078275525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746341722388806771034033 559756291791605078275525)
                ·
                  refine ⟨104954304710925952176661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559756291791605078275525 104954304710925952176661)
                  ·
                    rfl

theorem cell21_459895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_459895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459895 prefixEnd_459895 := by exact prefixLift 459895
  have htrace : WordTrace (prefixWord ++ tailWord_459895) baseStart_459895 baseEnd_459895 := by
    simpa [prefixWord, tailWord_459895, baseEnd_459895] using wordTrace_append hprefix tailTrace_459895
  have hstable : (prefixWord ++ tailWord_459895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459895).length < 2 ^ (prefixWord ++ tailWord_459895).sum := by decide
  have hdescent : baseEnd_459895 < baseStart_459895 := by decide
  rcases family_descends (prefixWord ++ tailWord_459895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459923 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_459923 : Nat := 118140960795 + 459923 * 2 ^ 59
def prefixEnd_459923 : Nat := 4983230072969 + 3 ^ 40 * 459923 * 2
def baseEnd_459923 : Nat := 104960694692404125709937

theorem tailTrace_459923 : CollatzResearch.WordTrace tailWord_459923 prefixEnd_459923 104960694692404125709937 := by
  unfold tailWord_459923
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774769912784994439936423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11183179941856662959957615 16774769912784994439936423)
  ·
    refine ⟨25162154869177491659904635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16774769912784994439936423 25162154869177491659904635)
    ·
      refine ⟨37743232303766237489856953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25162154869177491659904635 37743232303766237489856953)
      ·
        refine ⟨28307424227824678117392715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37743232303766237489856953 28307424227824678117392715)
        ·
          refine ⟨42461136341737017176089073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28307424227824678117392715 42461136341737017176089073)
          ·
            refine ⟨31845852256302762882066805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42461136341737017176089073 31845852256302762882066805)
            ·
              refine ⟨2985548649028384020193763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31845852256302762882066805 2985548649028384020193763)
              ·
                refine ⟨4478322973542576030290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985548649028384020193763 4478322973542576030290645)
                ·
                  refine ⟨104960694692404125709937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4478322973542576030290645 104960694692404125709937)
                  ·
                    rfl

theorem cell21_459923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_459923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459923 prefixEnd_459923 := by exact prefixLift 459923
  have htrace : WordTrace (prefixWord ++ tailWord_459923) baseStart_459923 baseEnd_459923 := by
    simpa [prefixWord, tailWord_459923, baseEnd_459923] using wordTrace_append hprefix tailTrace_459923
  have hstable : (prefixWord ++ tailWord_459923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459923).length < 2 ^ (prefixWord ++ tailWord_459923).sum := by decide
  have hdescent : baseEnd_459923 < baseStart_459923 := by decide
  rcases family_descends (prefixWord ++ tailWord_459923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459999 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_459999 : Nat := 118140960795 + 459999 * 2 ^ 59
def prefixEnd_459999 : Nat := 4983230072969 + 3 ^ 40 * 459999 * 2
def baseEnd_459999 : Nat := 104978038927844882443115

theorem tailTrace_459999 : CollatzResearch.WordTrace tailWord_459999 prefixEnd_459999 104978038927844882443115 := by
  unfold tailWord_459999
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777541860509659419703051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11185027907006439613135367 16777541860509659419703051)
  ·
    refine ⟨25166312790764489129554577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16777541860509659419703051 25166312790764489129554577)
    ·
      refine ⟨18874734593073366847165933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25166312790764489129554577 18874734593073366847165933)
      ·
        refine ⟨7078025472402512567687225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18874734593073366847165933 7078025472402512567687225)
        ·
          refine ⟨5308519104301884425765419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7078025472402512567687225 5308519104301884425765419)
          ·
            refine ⟨7962778656452826638648129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308519104301884425765419 7962778656452826638648129)
            ·
              refine ⟨5972083992339619978986097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962778656452826638648129 5972083992339619978986097)
              ·
                refine ⟨4479062994254714984239573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5972083992339619978986097 4479062994254714984239573)
                ·
                  refine ⟨104978038927844882443115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4479062994254714984239573 104978038927844882443115)
                  ·
                    rfl

theorem cell21_459999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_459999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459999 prefixEnd_459999 := by exact prefixLift 459999
  have htrace : WordTrace (prefixWord ++ tailWord_459999) baseStart_459999 baseEnd_459999 := by
    simpa [prefixWord, tailWord_459999, baseEnd_459999] using wordTrace_append hprefix tailTrace_459999
  have hstable : (prefixWord ++ tailWord_459999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459999).length < 2 ^ (prefixWord ++ tailWord_459999).sum := by decide
  have hdescent : baseEnd_459999 < baseStart_459999 := by decide
  rcases family_descends (prefixWord ++ tailWord_459999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460061 : List Nat := [1, 4, 2, 3, 1, 10]
def baseStart_460061 : Nat := 118140960795 + 460061 * 2 ^ 59
def prefixEnd_460061 : Nat := 4983230072969 + 3 ^ 40 * 460061 * 2
def baseEnd_460061 : Nat := 3888599561946168607765

theorem tailTrace_460061 : CollatzResearch.WordTrace tailWord_460061 prefixEnd_460061 3888599561946168607765 := by
  unfold tailWord_460061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779803186285044008460037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186535457523362672306691 16779803186285044008460037)
  ·
    refine ⟨3146213097428445751586257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16779803186285044008460037 3146213097428445751586257)
    ·
      refine ⟨2359659823071334313689693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3146213097428445751586257 2359659823071334313689693)
      ·
        refine ⟨884872433651750367633635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2359659823071334313689693 884872433651750367633635)
        ·
          refine ⟨1327308650477625551450453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884872433651750367633635 1327308650477625551450453)
          ·
            refine ⟨3888599561946168607765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1327308650477625551450453 3888599561946168607765)
            ·
              rfl

theorem cell21_460061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 10].length) (baseStart_460061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460061 prefixEnd_460061 := by exact prefixLift 460061
  have htrace : WordTrace (prefixWord ++ tailWord_460061) baseStart_460061 baseEnd_460061 := by
    simpa [prefixWord, tailWord_460061, baseEnd_460061] using wordTrace_append hprefix tailTrace_460061
  have hstable : (prefixWord ++ tailWord_460061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460061).length < 2 ^ (prefixWord ++ tailWord_460061).sum := by decide
  have hdescent : baseEnd_460061 < baseStart_460061 := by decide
  rcases family_descends (prefixWord ++ tailWord_460061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460064 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_460064 : Nat := 118140960795 + 460064 * 2 ^ 59
def prefixEnd_460064 : Nat := 4983230072969 + 3 ^ 40 * 460064 * 2
def baseEnd_460064 : Nat := 104992872813419213859649

theorem tailTrace_460064 : CollatzResearch.WordTrace tailWord_460064 prefixEnd_460064 104992872813419213859649 := by
  unfold tailWord_460064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389956302637087760409623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11186608403516117013879497 8389956302637087760409623)
  ·
    refine ⟨12584934453955631640614435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8389956302637087760409623 12584934453955631640614435)
    ·
      refine ⟨18877401680933447460921653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12584934453955631640614435 18877401680933447460921653)
      ·
        refine ⟨1769756407587510699461405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18877401680933447460921653 1769756407587510699461405)
        ·
          refine ⟨663658652845316512298027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1769756407587510699461405 663658652845316512298027)
          ·
            refine ⟨995487979267974768447041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663658652845316512298027 995487979267974768447041)
            ·
              refine ⟨746615984450981076335281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995487979267974768447041 746615984450981076335281)
              ·
                refine ⟨559961988338235807251461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746615984450981076335281 559961988338235807251461)
                ·
                  refine ⟨104992872813419213859649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559961988338235807251461 104992872813419213859649)
                  ·
                    rfl

theorem cell21_460064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_460064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460064 prefixEnd_460064 := by exact prefixLift 460064
  have htrace : WordTrace (prefixWord ++ tailWord_460064) baseStart_460064 baseEnd_460064 := by
    simpa [prefixWord, tailWord_460064, baseEnd_460064] using wordTrace_append hprefix tailTrace_460064
  have hstable : (prefixWord ++ tailWord_460064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460064).length < 2 ^ (prefixWord ++ tailWord_460064).sum := by decide
  have hdescent : baseEnd_460064 < baseStart_460064 := by decide
  rcases family_descends (prefixWord ++ tailWord_460064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460092 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_460092 : Nat := 118140960795 + 460092 * 2 ^ 59
def prefixEnd_460092 : Nat := 4983230072969 + 3 ^ 40 * 460092 * 2
def baseEnd_460092 : Nat := 104999262794897387392925

theorem tailTrace_460092 : CollatzResearch.WordTrace tailWord_460092 prefixEnd_460092 104999262794897387392925 := by
  unfold tailWord_460092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390466924586368151419265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11187289232781824201892353 8390466924586368151419265)
  ·
    refine ⟨6292850193439776113564449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8390466924586368151419265 6292850193439776113564449)
    ·
      refine ⟨4719637645079832085173337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6292850193439776113564449 4719637645079832085173337)
      ·
        refine ⟨3539728233809874063880003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719637645079832085173337 3539728233809874063880003)
        ·
          refine ⟨5309592350714811095820005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539728233809874063880003 5309592350714811095820005)
          ·
            refine ⟨995548565759027080466251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5309592350714811095820005 995548565759027080466251)
            ·
              refine ⟨1493322848638540620699377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995548565759027080466251 1493322848638540620699377)
              ·
                refine ⟨1119992136478905465524533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493322848638540620699377 1119992136478905465524533)
                ·
                  refine ⟨104999262794897387392925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119992136478905465524533 104999262794897387392925)
                  ·
                    rfl

theorem cell21_460092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_460092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460092 prefixEnd_460092 := by exact prefixLift 460092
  have htrace : WordTrace (prefixWord ++ tailWord_460092) baseStart_460092 baseEnd_460092 := by
    simpa [prefixWord, tailWord_460092, baseEnd_460092] using wordTrace_append hprefix tailTrace_460092
  have hstable : (prefixWord ++ tailWord_460092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460092).length < 2 ^ (prefixWord ++ tailWord_460092).sum := by decide
  have hdescent : baseEnd_460092 < baseStart_460092 := by decide
  rcases family_descends (prefixWord ++ tailWord_460092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460120 : List Nat := [2, 1, 2, 2, 1, 1, 12]
def baseStart_460120 : Nat := 118140960795 + 460120 * 2 ^ 59
def prefixEnd_460120 : Nat := 4983230072969 + 3 ^ 40 * 460120 * 2
def baseEnd_460120 : Nat := 11667294752930617880689

theorem tailTrace_460120 : CollatzResearch.WordTrace tailWord_460120 prefixEnd_460120 11667294752930617880689 := by
  unfold tailWord_460120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390977546535648542428907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11187970062047531389905209 8390977546535648542428907)
  ·
    refine ⟨12586466319803472813643361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8390977546535648542428907 12586466319803472813643361)
    ·
      refine ⟨9439849739852604610232521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12586466319803472813643361 9439849739852604610232521)
      ·
        refine ⟨7079887304889453457674391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9439849739852604610232521 7079887304889453457674391)
        ·
          refine ⟨10619830957334180186511587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7079887304889453457674391 10619830957334180186511587)
          ·
            refine ⟨15929746436001270279767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619830957334180186511587 15929746436001270279767381)
            ·
              refine ⟨11667294752930617880689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15929746436001270279767381 11667294752930617880689)
              ·
                rfl

theorem cell21_460120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 12].length) (baseStart_460120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460120 prefixEnd_460120 := by exact prefixLift 460120
  have htrace : WordTrace (prefixWord ++ tailWord_460120) baseStart_460120 baseEnd_460120 := by
    simpa [prefixWord, tailWord_460120, baseEnd_460120] using wordTrace_append hprefix tailTrace_460120
  have hstable : (prefixWord ++ tailWord_460120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460120).length < 2 ^ (prefixWord ++ tailWord_460120).sum := by decide
  have hdescent : baseEnd_460120 < baseStart_460120 := by decide
  rcases family_descends (prefixWord ++ tailWord_460120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460140 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_460140 : Nat := 118140960795 + 460140 * 2 ^ 59
def prefixEnd_460140 : Nat := 4983230072969 + 3 ^ 40 * 460140 * 2
def baseEnd_460140 : Nat := 105010217048859970592827

theorem tailTrace_460140 : CollatzResearch.WordTrace tailWord_460140 prefixEnd_460140 105010217048859970592827 := by
  unfold tailWord_460140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391342276499420250292937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11188456368665893667057249 8391342276499420250292937)
  ·
    refine ⟨6293506707374565187719703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8391342276499420250292937 6293506707374565187719703)
    ·
      refine ⟨9440260061061847781579555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6293506707374565187719703 9440260061061847781579555)
      ·
        refine ⟨14160390091592771672369333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440260061061847781579555 14160390091592771672369333)
        ·
          refine ⟨1327536571086822344284625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14160390091592771672369333 1327536571086822344284625)
          ·
            refine ⟨995652428315116758213469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327536571086822344284625 995652428315116758213469)
            ·
              refine ⟨373369660618168784330051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995652428315116758213469 373369660618168784330051)
              ·
                refine ⟨560054490927253176495077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373369660618168784330051 560054490927253176495077)
                ·
                  refine ⟨105010217048859970592827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560054490927253176495077 105010217048859970592827)
                  ·
                    rfl

theorem cell21_460140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_460140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460140 prefixEnd_460140 := by exact prefixLift 460140
  have htrace : WordTrace (prefixWord ++ tailWord_460140) baseStart_460140 baseEnd_460140 := by
    simpa [prefixWord, tailWord_460140, baseEnd_460140] using wordTrace_append hprefix tailTrace_460140
  have hstable : (prefixWord ++ tailWord_460140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460140).length < 2 ^ (prefixWord ++ tailWord_460140).sum := by decide
  have hdescent : baseEnd_460140 < baseStart_460140 := by decide
  rcases family_descends (prefixWord ++ tailWord_460140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460151 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_460151 : Nat := 118140960795 + 460151 * 2 ^ 59
def prefixEnd_460151 : Nat := 4983230072969 + 3 ^ 40 * 460151 * 2
def baseEnd_460151 : Nat := 105012727398726395909471

theorem tailTrace_460151 : CollatzResearch.WordTrace tailWord_460151 prefixEnd_460151 105012727398726395909471 := by
  unfold tailWord_460151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783085755958989379236307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188723837305992919490871 16783085755958989379236307)
  ·
    refine ⟨25174628633938484068854461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16783085755958989379236307 25174628633938484068854461)
    ·
      refine ⟨9440485737726931525820423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25174628633938484068854461 9440485737726931525820423)
      ·
        refine ⟨14160728606590397288730635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440485737726931525820423 14160728606590397288730635)
        ·
          refine ⟨21241092909885595933095953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14160728606590397288730635 21241092909885595933095953)
          ·
            refine ⟨15930819682414196949821965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21241092909885595933095953 15930819682414196949821965)
            ·
              refine ⟨5974057380905323856183237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15930819682414196949821965 5974057380905323856183237)
              ·
                refine ⟨1120135758919748223034357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5974057380905323856183237 1120135758919748223034357)
                ·
                  refine ⟨105012727398726395909471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120135758919748223034357 105012727398726395909471)
                  ·
                    rfl

theorem cell21_460151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_460151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460151 prefixEnd_460151 := by exact prefixLift 460151
  have htrace : WordTrace (prefixWord ++ tailWord_460151) baseStart_460151 baseEnd_460151 := by
    simpa [prefixWord, tailWord_460151, baseEnd_460151] using wordTrace_append hprefix tailTrace_460151
  have hstable : (prefixWord ++ tailWord_460151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460151).length < 2 ^ (prefixWord ++ tailWord_460151).sum := by decide
  have hdescent : baseEnd_460151 < baseStart_460151 := by decide
  rcases family_descends (prefixWord ++ tailWord_460151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460199 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_460199 : Nat := 118140960795 + 460199 * 2 ^ 59
def prefixEnd_460199 : Nat := 4983230072969 + 3 ^ 40 * 460199 * 2
def baseEnd_460199 : Nat := 105023681652688979109373

theorem tailTrace_460199 : CollatzResearch.WordTrace tailWord_460199 prefixEnd_460199 105023681652688979109373 := by
  unfold tailWord_460199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784836459785093576983651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11189890973190062384655767 16784836459785093576983651)
  ·
    refine ⟨25177254689677640365475477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784836459785093576983651 25177254689677640365475477)
    ·
      refine ⟨1180183813578639392131663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25177254689677640365475477 1180183813578639392131663)
      ·
        refine ⟨1770275720367959088197495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180183813578639392131663 1770275720367959088197495)
        ·
          refine ⟨2655413580551938632296243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770275720367959088197495 2655413580551938632296243)
          ·
            refine ⟨3983120370827907948444365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655413580551938632296243 3983120370827907948444365)
            ·
              refine ⟨1493670139060465480666637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3983120370827907948444365 1493670139060465480666637)
              ·
                refine ⟨560126302147674555249989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493670139060465480666637 560126302147674555249989)
                ·
                  refine ⟨105023681652688979109373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560126302147674555249989 105023681652688979109373)
                  ·
                    rfl

theorem cell21_460199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_460199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460199 prefixEnd_460199 := by exact prefixLift 460199
  have htrace : WordTrace (prefixWord ++ tailWord_460199) baseStart_460199 baseEnd_460199 := by
    simpa [prefixWord, tailWord_460199, baseEnd_460199] using wordTrace_append hprefix tailTrace_460199
  have hstable : (prefixWord ++ tailWord_460199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460199).length < 2 ^ (prefixWord ++ tailWord_460199).sum := by decide
  have hdescent : baseEnd_460199 < baseStart_460199 := by decide
  rcases family_descends (prefixWord ++ tailWord_460199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460213 : List Nat := [1, 3, 3, 2, 2, 1, 2, 7]
def baseStart_460213 : Nat := 118140960795 + 460213 * 2 ^ 59
def prefixEnd_460213 : Nat := 4983230072969 + 3 ^ 40 * 460213 * 2
def baseEnd_460213 : Nat := 35008958881142688625337

theorem tailTrace_460213 : CollatzResearch.WordTrace tailWord_460213 prefixEnd_460213 35008958881142688625337 := by
  unfold tailWord_460213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16785347081734373967993293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11190231387822915978662195 16785347081734373967993293)
  ·
    refine ⟨6294505155650390237997485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16785347081734373967993293 6294505155650390237997485)
    ·
      refine ⟨2360439433368896339249057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6294505155650390237997485 2360439433368896339249057)
      ·
        refine ⟨1770329575026672254436793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360439433368896339249057 1770329575026672254436793)
        ·
          refine ⟨1327747181270004190827595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770329575026672254436793 1327747181270004190827595)
          ·
            refine ⟨1991620771905006286241393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327747181270004190827595 1991620771905006286241393)
            ·
              refine ⟨1493715578928754714681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991620771905006286241393 1493715578928754714681045)
              ·
                refine ⟨35008958881142688625337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1493715578928754714681045 35008958881142688625337)
                ·
                  rfl

theorem cell21_460213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_460213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460213 prefixEnd_460213 := by exact prefixLift 460213
  have htrace : WordTrace (prefixWord ++ tailWord_460213) baseStart_460213 baseEnd_460213 := by
    simpa [prefixWord, tailWord_460213, baseEnd_460213] using wordTrace_append hprefix tailTrace_460213
  have hstable : (prefixWord ++ tailWord_460213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460213).length < 2 ^ (prefixWord ++ tailWord_460213).sum := by decide
  have hdescent : baseEnd_460213 < baseStart_460213 := by decide
  rcases family_descends (prefixWord ++ tailWord_460213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460278 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_460278 : Nat := 118140960795 + 460278 * 2 ^ 59
def prefixEnd_460278 : Nat := 4983230072969 + 3 ^ 40 * 460278 * 2
def baseEnd_460278 : Nat := 105041710529002397292545

theorem tailTrace_460278 : CollatzResearch.WordTrace tailWord_460278 prefixEnd_460278 105041710529002397292545 := by
  unfold tailWord_460278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049232364156180629319343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11191811884332593379406325 1049232364156180629319343)
  ·
    refine ⟨1573848546234270943979015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049232364156180629319343 1573848546234270943979015)
    ·
      refine ⟨2360772819351406415968523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573848546234270943979015 2360772819351406415968523)
      ·
        refine ⟨3541159229027109623952785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360772819351406415968523 3541159229027109623952785)
        ·
          refine ⟨2655869421770332217964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541159229027109623952785 2655869421770332217964589)
          ·
            refine ⟨995951033163874581736721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655869421770332217964589 995951033163874581736721)
            ·
              refine ⟨746963274872905936302541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995951033163874581736721 746963274872905936302541)
              ·
                refine ⟨280111228077339726113453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746963274872905936302541 280111228077339726113453)
                ·
                  refine ⟨105041710529002397292545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280111228077339726113453 105041710529002397292545)
                  ·
                    rfl

theorem cell21_460278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_460278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460278 prefixEnd_460278 := by exact prefixLift 460278
  have htrace : WordTrace (prefixWord ++ tailWord_460278) baseStart_460278 baseEnd_460278 := by
    simpa [prefixWord, tailWord_460278, baseEnd_460278] using wordTrace_append hprefix tailTrace_460278
  have hstable : (prefixWord ++ tailWord_460278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460278).length < 2 ^ (prefixWord ++ tailWord_460278).sum := by decide
  have hdescent : baseEnd_460278 < baseStart_460278 := by decide
  rcases family_descends (prefixWord ++ tailWord_460278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460289 : List Nat := [1, 2, 4, 1, 4, 1, 8]
def baseStart_460289 : Nat := 118140960795 + 460289 * 2 ^ 59
def prefixEnd_460289 : Nat := 4983230072969 + 3 ^ 40 * 460289 * 2
def baseEnd_460289 : Nat := 11671580097652091401021

theorem tailTrace_460289 : CollatzResearch.WordTrace tailWord_460289 prefixEnd_460289 11671580097652091401021 := by
  unfold tailWord_460289
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788119029459038947759921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11192079352972692631839947 16788119029459038947759921)
  ·
    refine ⟨12591089272094279210819941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16788119029459038947759921 12591089272094279210819941)
    ·
      refine ⟨2360829238517677352028739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12591089272094279210819941 2360829238517677352028739)
      ·
        refine ⟨3541243857776516028043109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360829238517677352028739 3541243857776516028043109)
        ·
          refine ⟨663983223333096755258083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3541243857776516028043109 663983223333096755258083)
          ·
            refine ⟨995974834999645132887125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663983223333096755258083 995974834999645132887125)
            ·
              refine ⟨11671580097652091401021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 995974834999645132887125 11671580097652091401021)
              ·
                rfl

theorem cell21_460289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 8].length) (baseStart_460289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460289 prefixEnd_460289 := by exact prefixLift 460289
  have htrace : WordTrace (prefixWord ++ tailWord_460289) baseStart_460289 baseEnd_460289 := by
    simpa [prefixWord, tailWord_460289, baseEnd_460289] using wordTrace_append hprefix tailTrace_460289
  have hstable : (prefixWord ++ tailWord_460289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460289).length < 2 ^ (prefixWord ++ tailWord_460289).sum := by decide
  have hdescent : baseEnd_460289 < baseStart_460289 := by decide
  rcases family_descends (prefixWord ++ tailWord_460289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460320 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_460320 : Nat := 118140960795 + 460320 * 2 ^ 59
def prefixEnd_460320 : Nat := 4983230072969 + 3 ^ 40 * 460320 * 2
def baseEnd_460320 : Nat := 105051295501219657592459

theorem tailTrace_460320 : CollatzResearch.WordTrace tailWord_460320 prefixEnd_460320 105051295501219657592459 := by
  unfold tailWord_460320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394624846173365621069207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11192833128231154161425609 8394624846173365621069207)
  ·
    refine ⟨12591937269260048431603811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8394624846173365621069207 12591937269260048431603811)
    ·
      refine ⟨18887905903890072647405717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591937269260048431603811 18887905903890072647405717)
      ·
        refine ⟨885370589244847155347143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18887905903890072647405717 885370589244847155347143)
        ·
          refine ⟨1328055883867270733020715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885370589244847155347143 1328055883867270733020715)
          ·
            refine ⟨1992083825800906099531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328055883867270733020715 1992083825800906099531073)
            ·
              refine ⟨1494062869350679574648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992083825800906099531073 1494062869350679574648305)
              ·
                refine ⟨1120547152013009680986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494062869350679574648305 1120547152013009680986229)
                ·
                  refine ⟨105051295501219657592459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120547152013009680986229 105051295501219657592459)
                  ·
                    rfl

theorem cell21_460320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_460320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460320 prefixEnd_460320 := by exact prefixLift 460320
  have htrace : WordTrace (prefixWord ++ tailWord_460320) baseStart_460320 baseEnd_460320 := by
    simpa [prefixWord, tailWord_460320, baseEnd_460320] using wordTrace_append hprefix tailTrace_460320
  have hstable : (prefixWord ++ tailWord_460320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460320).length < 2 ^ (prefixWord ++ tailWord_460320).sum := by decide
  have hdescent : baseEnd_460320 < baseStart_460320 := by decide
  rcases family_descends (prefixWord ++ tailWord_460320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460323 : List Nat := [1, 1, 1, 4, 6, 1, 2, 5]
def baseStart_460323 : Nat := 118140960795 + 460323 * 2 ^ 59
def prefixEnd_460323 : Nat := 4983230072969 + 3 ^ 40 * 460323 * 2
def baseEnd_460323 : Nat := 35017326714030773014151

theorem tailTrace_460323 : CollatzResearch.WordTrace tailWord_460323 prefixEnd_460323 35017326714030773014151 := by
  unfold tailWord_460323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16789359111335862754497623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11192906074223908502998415 16789359111335862754497623)
  ·
    refine ⟨25184038667003794131746435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16789359111335862754497623 25184038667003794131746435)
    ·
      refine ⟨37776058000505691197619653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25184038667003794131746435 37776058000505691197619653)
      ·
        refine ⟨7083010875094817099553685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37776058000505691197619653 7083010875094817099553685)
        ·
          refine ⟨332016134770069551541579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7083010875094817099553685 332016134770069551541579)
          ·
            refine ⟨498024202155104327312369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332016134770069551541579 498024202155104327312369)
            ·
              refine ⟨373518151616328245484277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498024202155104327312369 373518151616328245484277)
              ·
                refine ⟨35017326714030773014151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373518151616328245484277 35017326714030773014151)
                ·
                  rfl

theorem cell21_460323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].length) (baseStart_460323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460323 prefixEnd_460323 := by exact prefixLift 460323
  have htrace : WordTrace (prefixWord ++ tailWord_460323) baseStart_460323 baseEnd_460323 := by
    simpa [prefixWord, tailWord_460323, baseEnd_460323] using wordTrace_append hprefix tailTrace_460323
  have hstable : (prefixWord ++ tailWord_460323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460323).length < 2 ^ (prefixWord ++ tailWord_460323).sum := by decide
  have hdescent : baseEnd_460323 < baseStart_460323 := by decide
  rcases family_descends (prefixWord ++ tailWord_460323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460393 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_460393 : Nat := 118140960795 + 460393 * 2 ^ 59
def prefixEnd_460393 : Nat := 4983230072969 + 3 ^ 40 * 460393 * 2
def baseEnd_460393 : Nat := 105067955095787752875643

theorem tailTrace_460393 : CollatzResearch.WordTrace tailWord_460393 prefixEnd_460393 105067955095787752875643 := by
  unfold tailWord_460393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791912221082264709545833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11194608147388176473030555 16791912221082264709545833)
  ·
    refine ⟨12593934165811698532159375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16791912221082264709545833 12593934165811698532159375)
    ·
      refine ⟨18890901248717547798239063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12593934165811698532159375 18890901248717547798239063)
      ·
        refine ⟨28336351873076321697358595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18890901248717547798239063 28336351873076321697358595)
        ·
          refine ⟨42504527809614482546037893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28336351873076321697358595 42504527809614482546037893)
          ·
            refine ⟨7969598964302715477382105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42504527809614482546037893 7969598964302715477382105)
            ·
              refine ⟨5977199223227036608036579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7969598964302715477382105 5977199223227036608036579)
              ·
                refine ⟨8965798834840554912054869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977199223227036608036579 8965798834840554912054869)
                ·
                  refine ⟨105067955095787752875643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8965798834840554912054869 105067955095787752875643)
                  ·
                    rfl

theorem cell21_460393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_460393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460393 prefixEnd_460393 := by exact prefixLift 460393
  have htrace : WordTrace (prefixWord ++ tailWord_460393) baseStart_460393 baseEnd_460393 := by
    simpa [prefixWord, tailWord_460393, baseEnd_460393] using wordTrace_append hprefix tailTrace_460393
  have hstable : (prefixWord ++ tailWord_460393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460393).length < 2 ^ (prefixWord ++ tailWord_460393).sum := by decide
  have hdescent : baseEnd_460393 < baseStart_460393 := by decide
  rcases family_descends (prefixWord ++ tailWord_460393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_460396 : Nat := 118140960795 + 460396 * 2 ^ 59
def prefixEnd_460396 : Nat := 4983230072969 + 3 ^ 40 * 460396 * 2
def baseEnd_460396 : Nat := 105068639736660414325637

theorem tailTrace_460396 : CollatzResearch.WordTrace tailWord_460396 prefixEnd_460396 105068639736660414325637 := by
  unfold tailWord_460396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396010820035698110952521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11194681093380930814603361 8396010820035698110952521)
  ·
    refine ⟨6297008115026773583214391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8396010820035698110952521 6297008115026773583214391)
    ·
      refine ⟨9445512172540160374821587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6297008115026773583214391 9445512172540160374821587)
      ·
        refine ⟨14168268258810240562232381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445512172540160374821587 14168268258810240562232381)
        ·
          refine ⟨5313100597053840210837143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14168268258810240562232381 5313100597053840210837143)
          ·
            refine ⟨7969650895580760316255715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313100597053840210837143 7969650895580760316255715)
            ·
              refine ⟨11954476343371140474383573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969650895580760316255715 11954476343371140474383573)
              ·
                refine ⟨280183039297761104868365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11954476343371140474383573 280183039297761104868365)
                ·
                  refine ⟨105068639736660414325637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280183039297761104868365 105068639736660414325637)
                  ·
                    rfl

theorem cell21_460396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_460396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460396 prefixEnd_460396 := by exact prefixLift 460396
  have htrace : WordTrace (prefixWord ++ tailWord_460396) baseStart_460396 baseEnd_460396 := by
    simpa [prefixWord, tailWord_460396, baseEnd_460396] using wordTrace_append hprefix tailTrace_460396
  have hstable : (prefixWord ++ tailWord_460396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460396).length < 2 ^ (prefixWord ++ tailWord_460396).sum := by decide
  have hdescent : baseEnd_460396 < baseStart_460396 := by decide
  rcases family_descends (prefixWord ++ tailWord_460396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460413 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 3]
def baseStart_460413 : Nat := 118140960795 + 460413 * 2 ^ 59
def prefixEnd_460413 : Nat := 4983230072969 + 3 ^ 40 * 460413 * 2
def baseEnd_460413 : Nat := 105072519368272162542269

theorem tailTrace_460413 : CollatzResearch.WordTrace tailWord_460413 prefixEnd_460413 105072519368272162542269 := by
  unfold tailWord_460413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16792641681009808125273893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11195094454006538750182595 16792641681009808125273893)
  ·
    refine ⟨3148620315189339023488855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16792641681009808125273893 3148620315189339023488855)
    ·
      refine ⟨4722930472784008535233283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148620315189339023488855 4722930472784008535233283)
      ·
        refine ⟨7084395709176012802849925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722930472784008535233283 7084395709176012802849925)
        ·
          refine ⟨1328324195470502400534361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7084395709176012802849925 1328324195470502400534361)
          ·
            refine ⟨996243146602876800400771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328324195470502400534361 996243146602876800400771)
            ·
              refine ⟨1494364719904315200601157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996243146602876800400771 1494364719904315200601157)
              ·
                refine ⟨280193384982059100112717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1494364719904315200601157 280193384982059100112717)
                ·
                  refine ⟨105072519368272162542269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280193384982059100112717 105072519368272162542269)
                  ·
                    rfl

theorem cell21_460413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_460413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460413 prefixEnd_460413 := by exact prefixLift 460413
  have htrace : WordTrace (prefixWord ++ tailWord_460413) baseStart_460413 baseEnd_460413 := by
    simpa [prefixWord, tailWord_460413, baseEnd_460413] using wordTrace_append hprefix tailTrace_460413
  have hstable : (prefixWord ++ tailWord_460413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460413).length < 2 ^ (prefixWord ++ tailWord_460413).sum := by decide
  have hdescent : baseEnd_460413 < baseStart_460413 := by decide
  rcases family_descends (prefixWord ++ tailWord_460413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460531 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_460531 : Nat := 118140960795 + 460531 * 2 ^ 59
def prefixEnd_460531 : Nat := 4983230072969 + 3 ^ 40 * 460531 * 2
def baseEnd_460531 : Nat := 105099448575930179575361

theorem tailTrace_460531 : CollatzResearch.WordTrace tailWord_460531 prefixEnd_460531 105099448575930179575361 := by
  unfold tailWord_460531
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796945494582314278069447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197963663054876185379631 16796945494582314278069447)
  ·
    refine ⟨25195418241873471417104171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16796945494582314278069447 25195418241873471417104171)
    ·
      refine ⟨37793127362810207125656257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25195418241873471417104171 37793127362810207125656257)
      ·
        refine ⟨28344845522107655344242193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37793127362810207125656257 28344845522107655344242193)
        ·
          refine ⟨21258634141580741508181645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28344845522107655344242193 21258634141580741508181645)
          ·
            refine ⟨7971987803092778065568117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21258634141580741508181645 7971987803092778065568117)
            ·
              refine ⟨747373856539947943647011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7971987803092778065568117 747373856539947943647011)
              ·
                refine ⟨1121060784809921915470517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747373856539947943647011 1121060784809921915470517)
                ·
                  refine ⟨105099448575930179575361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121060784809921915470517 105099448575930179575361)
                  ·
                    rfl

theorem cell21_460531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_460531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460531 prefixEnd_460531 := by exact prefixLift 460531
  have htrace : WordTrace (prefixWord ++ tailWord_460531) baseStart_460531 baseEnd_460531 := by
    simpa [prefixWord, tailWord_460531, baseEnd_460531] using wordTrace_append hprefix tailTrace_460531
  have hstable : (prefixWord ++ tailWord_460531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460531).length < 2 ^ (prefixWord ++ tailWord_460531).sum := by decide
  have hdescent : baseEnd_460531 < baseStart_460531 := by decide
  rcases family_descends (prefixWord ++ tailWord_460531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460593 : List Nat := [1, 2, 2, 3, 2, 4, 1, 6]
def baseStart_460593 : Nat := 118140960795 + 460593 * 2 ^ 59
def prefixEnd_460593 : Nat := 4983230072969 + 3 ^ 40 * 460593 * 2
def baseEnd_460593 : Nat := 35037865940210616513967

theorem tailTrace_460593 : CollatzResearch.WordTrace tailWord_460593 prefixEnd_460593 35037865940210616513967 := by
  unfold tailWord_460593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799206820357698866826433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11199471213571799244550955 16799206820357698866826433)
  ·
    refine ⟨12599405115268274150119825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16799206820357698866826433 12599405115268274150119825)
    ·
      refine ⟨9449553836451205612589869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12599405115268274150119825 9449553836451205612589869)
      ·
        refine ⟨3543582688669202104721201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9449553836451205612589869 3543582688669202104721201)
        ·
          refine ⟨2657687016501901578540901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543582688669202104721201 2657687016501901578540901)
          ·
            refine ⟨498316315594106545976419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2657687016501901578540901 498316315594106545976419)
            ·
              refine ⟨747474473391159818964629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498316315594106545976419 747474473391159818964629)
              ·
                refine ⟨35037865940210616513967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 747474473391159818964629 35037865940210616513967)
                ·
                  rfl

theorem cell21_460593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_460593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460593 prefixEnd_460593 := by exact prefixLift 460593
  have htrace : WordTrace (prefixWord ++ tailWord_460593) baseStart_460593 baseEnd_460593 := by
    simpa [prefixWord, tailWord_460593, baseEnd_460593] using wordTrace_append hprefix tailTrace_460593
  have hstable : (prefixWord ++ tailWord_460593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460593).length < 2 ^ (prefixWord ++ tailWord_460593).sum := by decide
  have hdescent : baseEnd_460593 < baseStart_460593 := by decide
  rcases family_descends (prefixWord ++ tailWord_460593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460686 : List Nat := [4, 1, 1, 5, 1, 2, 7]
def baseStart_460686 : Nat := 118140960795 + 460686 * 2 ^ 59
def prefixEnd_460686 : Nat := 4983230072969 + 3 ^ 40 * 460686 * 2
def baseEnd_460686 : Nat := 11681646854187150499079

theorem tailTrace_460686 : CollatzResearch.WordTrace tailWord_460686 prefixEnd_460686 11681646854187150499079 := by
  unfold tailWord_460686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100324851127596968745239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11201732539347183833307941 2100324851127596968745239)
  ·
    refine ⟨3150487276691395453117859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100324851127596968745239 3150487276691395453117859)
    ·
      refine ⟨4725730915037093179676789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150487276691395453117859 4725730915037093179676789)
      ·
        refine ⟨443037273284727485594699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4725730915037093179676789 443037273284727485594699)
        ·
          refine ⟨664555909927091228392049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443037273284727485594699 664555909927091228392049)
          ·
            refine ⟨498416932445318421294037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664555909927091228392049 498416932445318421294037)
            ·
              refine ⟨11681646854187150499079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498416932445318421294037 11681646854187150499079)
              ·
                rfl

theorem cell21_460686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 7].length) (baseStart_460686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460686 prefixEnd_460686 := by exact prefixLift 460686
  have htrace : WordTrace (prefixWord ++ tailWord_460686) baseStart_460686 baseEnd_460686 := by
    simpa [prefixWord, tailWord_460686, baseEnd_460686] using wordTrace_append hprefix tailTrace_460686
  have hstable : (prefixWord ++ tailWord_460686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460686).length < 2 ^ (prefixWord ++ tailWord_460686).sum := by decide
  have hdescent : baseEnd_460686 < baseStart_460686 := by decide
  rcases family_descends (prefixWord ++ tailWord_460686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460697 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_460697 : Nat := 118140960795 + 460697 * 2 ^ 59
def prefixEnd_460697 : Nat := 4983230072969 + 3 ^ 40 * 460697 * 2
def baseEnd_460697 : Nat := 105137332037550779808355

theorem tailTrace_460697 : CollatzResearch.WordTrace tailWord_460697 prefixEnd_460697 105137332037550779808355 := by
  unfold tailWord_460697
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803000011980924628612345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202000007987283085741563 16803000011980924628612345)
  ·
    refine ⟨12602250008985693471459259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16803000011980924628612345 12602250008985693471459259)
    ·
      refine ⟨18903375013478540207188889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602250008985693471459259 18903375013478540207188889)
      ·
        refine ⟨14177531260108905155391667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18903375013478540207188889 14177531260108905155391667)
        ·
          refine ⟨21266296890163357733087501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177531260108905155391667 21266296890163357733087501)
          ·
            refine ⟨7974861333811259149907813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21266296890163357733087501 7974861333811259149907813)
            ·
              refine ⟨1495286500089611090607715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7974861333811259149907813 1495286500089611090607715)
              ·
                refine ⟨2242929750134416635911573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495286500089611090607715 2242929750134416635911573)
                ·
                  refine ⟨105137332037550779808355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2242929750134416635911573 105137332037550779808355)
                  ·
                    rfl

theorem cell21_460697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_460697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460697 prefixEnd_460697 := by exact prefixLift 460697
  have htrace : WordTrace (prefixWord ++ tailWord_460697) baseStart_460697 baseEnd_460697 := by
    simpa [prefixWord, tailWord_460697, baseEnd_460697] using wordTrace_append hprefix tailTrace_460697
  have hstable : (prefixWord ++ tailWord_460697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460697).length < 2 ^ (prefixWord ++ tailWord_460697).sum := by decide
  have hdescent : baseEnd_460697 < baseStart_460697 := by decide
  rcases family_descends (prefixWord ++ tailWord_460697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460700 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_460700 : Nat := 118140960795 + 460700 * 2 ^ 59
def prefixEnd_460700 : Nat := 4983230072969 + 3 ^ 40 * 460700 * 2
def baseEnd_460700 : Nat := 105138016678423441258349

theorem tailTrace_460700 : CollatzResearch.WordTrace tailWord_460700 prefixEnd_460700 105138016678423441258349 := by
  unfold tailWord_460700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401554715485028070485777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11202072953980037427314369 8401554715485028070485777)
  ·
    refine ⟨6301166036613771052864333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8401554715485028070485777 6301166036613771052864333)
    ·
      refine ⟨2362937263730164144824125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6301166036613771052864333 2362937263730164144824125)
      ·
        refine ⟨886101473898811554309047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2362937263730164144824125 886101473898811554309047)
        ·
          refine ⟨1329152210848217331463571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886101473898811554309047 1329152210848217331463571)
          ·
            refine ⟨1993728316272325997195357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329152210848217331463571 1993728316272325997195357)
            ·
              refine ⟨747648118602122248948259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993728316272325997195357 747648118602122248948259)
              ·
                refine ⟨1121472177903183373422389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747648118602122248948259 1121472177903183373422389)
                ·
                  refine ⟨105138016678423441258349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121472177903183373422389 105138016678423441258349)
                  ·
                    rfl

theorem cell21_460700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_460700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460700 prefixEnd_460700 := by exact prefixLift 460700
  have htrace : WordTrace (prefixWord ++ tailWord_460700) baseStart_460700 baseEnd_460700 := by
    simpa [prefixWord, tailWord_460700, baseEnd_460700] using wordTrace_append hprefix tailTrace_460700
  have hstable : (prefixWord ++ tailWord_460700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460700).length < 2 ^ (prefixWord ++ tailWord_460700).sum := by decide
  have hdescent : baseEnd_460700 < baseStart_460700 := by decide
  rcases family_descends (prefixWord ++ tailWord_460700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460762 : List Nat := [3, 1, 1, 2, 6, 1, 1, 6]
def baseStart_460762 : Nat := 118140960795 + 460762 * 2 ^ 59
def prefixEnd_460762 : Nat := 4983230072969 + 3 ^ 40 * 460762 * 2
def baseEnd_460762 : Nat := 35050721974375037074963

theorem tailTrace_460762 : CollatzResearch.WordTrace tailWord_460762 prefixEnd_460762 35050721974375037074963 := by
  unfold tailWord_460762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201342689186360182432135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11203580504496960486485693 4201342689186360182432135)
  ·
    refine ⟨6302014033779540273648203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201342689186360182432135 6302014033779540273648203)
    ·
      refine ⟨9453021050669310410472305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302014033779540273648203 9453021050669310410472305)
      ·
        refine ⟨7089765788001982807854229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9453021050669310410472305 7089765788001982807854229)
        ·
          refine ⟨332332771312592944118167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7089765788001982807854229 332332771312592944118167)
          ·
            refine ⟨498499156968889416177251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332332771312592944118167 498499156968889416177251)
            ·
              refine ⟨747748735453334124265877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498499156968889416177251 747748735453334124265877)
              ·
                refine ⟨35050721974375037074963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 747748735453334124265877 35050721974375037074963)
                ·
                  rfl

theorem cell21_460762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_460762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460762 prefixEnd_460762 := by exact prefixLift 460762
  have htrace : WordTrace (prefixWord ++ tailWord_460762) baseStart_460762 baseEnd_460762 := by
    simpa [prefixWord, tailWord_460762, baseEnd_460762] using wordTrace_append hprefix tailTrace_460762
  have hstable : (prefixWord ++ tailWord_460762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460762).length < 2 ^ (prefixWord ++ tailWord_460762).sum := by decide
  have hdescent : baseEnd_460762 < baseStart_460762 := by decide
  rcases family_descends (prefixWord ++ tailWord_460762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460787 : List Nat := [1, 1, 1, 2, 2, 2, 1, 11]
def baseStart_460787 : Nat := 118140960795 + 460787 * 2 ^ 59
def prefixEnd_460787 : Nat := 4983230072969 + 3 ^ 40 * 460787 * 2
def baseEnd_460787 : Nat := 35052623754576874436057

theorem tailTrace_460787 : CollatzResearch.WordTrace tailWord_460787 prefixEnd_460787 35052623754576874436057 := by
  unfold tailWord_460787
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806282581654869999388615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11204188387769913332925743 16806282581654869999388615)
  ·
    refine ⟨25209423872482304999082923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16806282581654869999388615 25209423872482304999082923)
    ·
      refine ⟨37814135808723457498624385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25209423872482304999082923 37814135808723457498624385)
      ·
        refine ⟨28360601856542593123968289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37814135808723457498624385 28360601856542593123968289)
        ·
          refine ⟨21270451392406944842976217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28360601856542593123968289 21270451392406944842976217)
          ·
            refine ⟨15952838544305208632232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21270451392406944842976217 15952838544305208632232163)
            ·
              refine ⟨23929257816457812948348245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15952838544305208632232163 23929257816457812948348245)
              ·
                refine ⟨35052623754576874436057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23929257816457812948348245 35052623754576874436057)
                ·
                  rfl

theorem cell21_460787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_460787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460787 prefixEnd_460787 := by exact prefixLift 460787
  have htrace : WordTrace (prefixWord ++ tailWord_460787) baseStart_460787 baseEnd_460787 := by
    simpa [prefixWord, tailWord_460787, baseEnd_460787] using wordTrace_append hprefix tailTrace_460787
  have hstable : (prefixWord ++ tailWord_460787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460787).length < 2 ^ (prefixWord ++ tailWord_460787).sum := by decide
  have hdescent : baseEnd_460787 < baseStart_460787 := by decide
  rcases family_descends (prefixWord ++ tailWord_460787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460807 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_460807 : Nat := 118140960795 + 460807 * 2 ^ 59
def prefixEnd_460807 : Nat := 4983230072969 + 3 ^ 40 * 460807 * 2
def baseEnd_460807 : Nat := 105162435536215032974797

theorem tailTrace_460807 : CollatzResearch.WordTrace tailWord_460807 prefixEnd_460807 105162435536215032974797 := by
  unfold tailWord_460807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807012041582413415116675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11204674694388275610077783 16807012041582413415116675)
  ·
    refine ⟨25210518062373620122675013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16807012041582413415116675 25210518062373620122675013)
    ·
      refine ⟨4726972136695053773001565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25210518062373620122675013 4726972136695053773001565)
      ·
        refine ⟨1772614551260645164875587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4726972136695053773001565 1772614551260645164875587)
        ·
          refine ⟨2658921826890967747313381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772614551260645164875587 2658921826890967747313381)
          ·
            refine ⟨498547842542056452621259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2658921826890967747313381 498547842542056452621259)
            ·
              refine ⟨747821763813084678931889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498547842542056452621259 747821763813084678931889)
              ·
                refine ⟨560866322859813509198917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747821763813084678931889 560866322859813509198917)
                ·
                  refine ⟨105162435536215032974797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560866322859813509198917 105162435536215032974797)
                  ·
                    rfl

theorem cell21_460807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_460807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460807 prefixEnd_460807 := by exact prefixLift 460807
  have htrace : WordTrace (prefixWord ++ tailWord_460807) baseStart_460807 baseEnd_460807 := by
    simpa [prefixWord, tailWord_460807, baseEnd_460807] using wordTrace_append hprefix tailTrace_460807
  have hstable : (prefixWord ++ tailWord_460807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460807).length < 2 ^ (prefixWord ++ tailWord_460807).sum := by decide
  have hdescent : baseEnd_460807 < baseStart_460807 := by decide
  rcases family_descends (prefixWord ++ tailWord_460807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460849 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_460849 : Nat := 118140960795 + 460849 * 2 ^ 59
def prefixEnd_460849 : Nat := 4983230072969 + 3 ^ 40 * 460849 * 2
def baseEnd_460849 : Nat := 105172020508432293274711

theorem tailTrace_460849 : CollatzResearch.WordTrace tailWord_460849 prefixEnd_460849 105172020508432293274711 := by
  unfold tailWord_460849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808543907430254588145601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11205695938286836392097067 16808543907430254588145601)
  ·
    refine ⟨12606407930572690941109201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16808543907430254588145601 12606407930572690941109201)
    ·
      refine ⟨9454805947929518205831901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12606407930572690941109201 9454805947929518205831901)
      ·
        refine ⟨3545552230473569327186963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454805947929518205831901 3545552230473569327186963)
        ·
          refine ⟨5318328345710353990780445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545552230473569327186963 5318328345710353990780445)
          ·
            refine ⟨1994373129641382746542667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5318328345710353990780445 1994373129641382746542667)
            ·
              refine ⟨2991559694462074119814001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994373129641382746542667 2991559694462074119814001)
              ·
                refine ⟨2243669770846555589860501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991559694462074119814001 2243669770846555589860501)
                ·
                  refine ⟨105172020508432293274711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2243669770846555589860501 105172020508432293274711)
                  ·
                    rfl

theorem cell21_460849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_460849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460849 prefixEnd_460849 := by exact prefixLift 460849
  have htrace : WordTrace (prefixWord ++ tailWord_460849) baseStart_460849 baseEnd_460849 := by
    simpa [prefixWord, tailWord_460849, baseEnd_460849] using wordTrace_append hprefix tailTrace_460849
  have hstable : (prefixWord ++ tailWord_460849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460849).length < 2 ^ (prefixWord ++ tailWord_460849).sum := by decide
  have hdescent : baseEnd_460849 < baseStart_460849 := by decide
  rcases family_descends (prefixWord ++ tailWord_460849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460863 : List Nat := [1, 1, 2, 2, 3, 1, 11]
def baseStart_460863 : Nat := 118140960795 + 460863 * 2 ^ 59
def prefixEnd_460863 : Nat := 4983230072969 + 3 ^ 40 * 460863 * 2
def baseEnd_460863 : Nat := 11686135055463486671261

theorem tailTrace_460863 : CollatzResearch.WordTrace tailWord_460863 prefixEnd_460863 11686135055463486671261 := by
  unfold tailWord_460863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809054529379534979155243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11206036352919689986103495 16809054529379534979155243)
  ·
    refine ⟨25213581794069302468732865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809054529379534979155243 25213581794069302468732865)
    ·
      refine ⟨18910186345551976851549649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25213581794069302468732865 18910186345551976851549649)
      ·
        refine ⟨14182639759163982638662237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18910186345551976851549649 14182639759163982638662237)
        ·
          refine ⟨5318489909686493489498339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14182639759163982638662237 5318489909686493489498339)
          ·
            refine ⟨7977734864529740234247509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318489909686493489498339 7977734864529740234247509)
            ·
              refine ⟨11686135055463486671261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7977734864529740234247509 11686135055463486671261)
              ·
                rfl

theorem cell21_460863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_460863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460863 prefixEnd_460863 := by exact prefixLift 460863
  have htrace : WordTrace (prefixWord ++ tailWord_460863) baseStart_460863 baseEnd_460863 := by
    simpa [prefixWord, tailWord_460863, baseEnd_460863] using wordTrace_append hprefix tailTrace_460863
  have hstable : (prefixWord ++ tailWord_460863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460863).length < 2 ^ (prefixWord ++ tailWord_460863).sum := by decide
  have hdescent : baseEnd_460863 < baseStart_460863 := by decide
  rcases family_descends (prefixWord ++ tailWord_460863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460987 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 3]
def baseStart_460987 : Nat := 118140960795 + 460987 * 2 ^ 59
def prefixEnd_460987 : Nat := 4983230072969 + 3 ^ 40 * 460987 * 2
def baseEnd_460987 : Nat := 105203513988574719974429

theorem tailTrace_460987 : CollatzResearch.WordTrace tailWord_460987 prefixEnd_460987 105203513988574719974429 := by
  unfold tailWord_460987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813577180930304156669215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11209051453953536104446143 16813577180930304156669215)
  ·
    refine ⟨25220365771395456235003823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16813577180930304156669215 25220365771395456235003823)
    ·
      refine ⟨37830548657093184352505735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220365771395456235003823 37830548657093184352505735)
      ·
        refine ⟨56745822985639776528758603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37830548657093184352505735 56745822985639776528758603)
        ·
          refine ⟨85118734478459664793137905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56745822985639776528758603 85118734478459664793137905)
          ·
            refine ⟨63839050858844748594853429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85118734478459664793137905 63839050858844748594853429)
            ·
              refine ⟨5984911018016695180767509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63839050858844748594853429 5984911018016695180767509)
              ·
                refine ⟨280542703969532586598477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5984911018016695180767509 280542703969532586598477)
                ·
                  refine ⟨105203513988574719974429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280542703969532586598477 105203513988574719974429)
                  ·
                    rfl

theorem cell21_460987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].length) (baseStart_460987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_460987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_460987 prefixEnd_460987 := by exact prefixLift 460987
  have htrace : WordTrace (prefixWord ++ tailWord_460987) baseStart_460987 baseEnd_460987 := by
    simpa [prefixWord, tailWord_460987, baseEnd_460987] using wordTrace_append hprefix tailTrace_460987
  have hstable : (prefixWord ++ tailWord_460987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460987).length < 2 ^ (prefixWord ++ tailWord_460987).sum := by decide
  have hdescent : baseEnd_460987 < baseStart_460987 := by decide
  rcases family_descends (prefixWord ++ tailWord_460987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461021 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 3]
def baseStart_461021 : Nat := 118140960795 + 461021 * 2 ^ 59
def prefixEnd_461021 : Nat := 4983230072969 + 3 ^ 40 * 461021 * 2
def baseEnd_461021 : Nat := 105211273251798216407693

theorem tailTrace_461021 : CollatzResearch.WordTrace tailWord_461021 prefixEnd_461021 105211273251798216407693 := by
  unfold tailWord_461021
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814817262807127963406917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11209878175204751975604611 16814817262807127963406917)
  ·
    refine ⟨3152778236776336493138797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16814817262807127963406917 3152778236776336493138797)
    ·
      refine ⟨1182291838791126184927049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3152778236776336493138797 1182291838791126184927049)
      ·
        refine ⟨886718879093344638695287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182291838791126184927049 886718879093344638695287)
        ·
          refine ⟨1330078318640016958042931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886718879093344638695287 1330078318640016958042931)
          ·
            refine ⟨1995117477960025437064397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330078318640016958042931 1995117477960025437064397)
            ·
              refine ⟨748169054235009538899149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995117477960025437064397 748169054235009538899149)
              ·
                refine ⟨280563395338128577087181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748169054235009538899149 280563395338128577087181)
                ·
                  refine ⟨105211273251798216407693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280563395338128577087181 105211273251798216407693)
                  ·
                    rfl

theorem cell21_461021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_461021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461021 prefixEnd_461021 := by exact prefixLift 461021
  have htrace : WordTrace (prefixWord ++ tailWord_461021) baseStart_461021 baseEnd_461021 := by
    simpa [prefixWord, tailWord_461021, baseEnd_461021] using wordTrace_append hprefix tailTrace_461021
  have hstable : (prefixWord ++ tailWord_461021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461021).length < 2 ^ (prefixWord ++ tailWord_461021).sum := by decide
  have hdescent : baseEnd_461021 < baseStart_461021 := by decide
  rcases family_descends (prefixWord ++ tailWord_461021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461032 : List Nat := [2, 1, 4, 1, 2, 4, 7]
def baseStart_461032 : Nat := 118140960795 + 461032 * 2 ^ 59
def prefixEnd_461032 : Nat := 4983230072969 + 3 ^ 40 * 461032 * 2
def baseEnd_461032 : Nat := 11690420400184960191593

theorem tailTrace_461032 : CollatzResearch.WordTrace tailWord_461032 prefixEnd_461032 11690420400184960191593 := by
  unfold tailWord_461032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407609232883638421028675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11210145643844851228038233 8407609232883638421028675)
  ·
    refine ⟨12611413849325457631543013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8407609232883638421028675 12611413849325457631543013)
    ·
      refine ⟨2364640096748523305914315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12611413849325457631543013 2364640096748523305914315)
      ·
        refine ⟨3546960145122784958871473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364640096748523305914315 3546960145122784958871473)
        ·
          refine ⟨2660220108842088719153605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546960145122784958871473 2660220108842088719153605)
          ·
            refine ⟨498791270407891634841301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2660220108842088719153605 498791270407891634841301)
            ·
              refine ⟨11690420400184960191593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498791270407891634841301 11690420400184960191593)
              ·
                rfl

theorem cell21_461032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 7].length) (baseStart_461032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461032 prefixEnd_461032 := by exact prefixLift 461032
  have htrace : WordTrace (prefixWord ++ tailWord_461032) baseStart_461032 baseEnd_461032 := by
    simpa [prefixWord, tailWord_461032, baseEnd_461032] using wordTrace_append hprefix tailTrace_461032
  have hstable : (prefixWord ++ tailWord_461032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461032).length < 2 ^ (prefixWord ++ tailWord_461032).sum := by decide
  have hdescent : baseEnd_461032 < baseStart_461032 := by decide
  rcases family_descends (prefixWord ++ tailWord_461032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461260 : List Nat := [2, 2, 1, 4, 4, 8]
def baseStart_461260 : Nat := 118140960795 + 461260 * 2 ^ 59
def prefixEnd_461260 : Nat := 4983230072969 + 3 ^ 40 * 461260 * 2
def baseEnd_461260 : Nat := 3898733937332848589773

theorem tailTrace_461260 : CollatzResearch.WordTrace tailWord_461260 prefixEnd_461260 3898733937332848589773 := by
  unfold tailWord_461260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411767154470635890678617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11215689539294181187571489 8411767154470635890678617)
  ·
    refine ⟨6308825365852976918008963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8411767154470635890678617 6308825365852976918008963)
    ·
      refine ⟨9463238048779465377013445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308825365852976918008963 9463238048779465377013445)
      ·
        refine ⟨1774357134146149758190021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9463238048779465377013445 1774357134146149758190021)
        ·
          refine ⟨332691962652403079660629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1774357134146149758190021 332691962652403079660629)
          ·
            refine ⟨3898733937332848589773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 332691962652403079660629 3898733937332848589773)
            ·
              rfl

theorem cell21_461260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 8].length) (baseStart_461260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461260 prefixEnd_461260 := by exact prefixLift 461260
  have htrace : WordTrace (prefixWord ++ tailWord_461260) baseStart_461260 baseEnd_461260 := by
    simpa [prefixWord, tailWord_461260, baseEnd_461260] using wordTrace_append hprefix tailTrace_461260
  have hstable : (prefixWord ++ tailWord_461260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461260).length < 2 ^ (prefixWord ++ tailWord_461260).sum := by decide
  have hdescent : baseEnd_461260 < baseStart_461260 := by decide
  rcases family_descends (prefixWord ++ tailWord_461260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461274 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_461274 : Nat := 118140960795 + 461274 * 2 ^ 59
def prefixEnd_461274 : Nat := 4983230072969 + 3 ^ 40 * 461274 * 2
def baseEnd_461274 : Nat := 105269011298725998690509

theorem tailTrace_461274 : CollatzResearch.WordTrace tailWord_461274 prefixEnd_461274 105269011298725998690509 := by
  unfold tailWord_461274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206011232722638043091719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11216029953927034781577917 4206011232722638043091719)
  ·
    refine ⟨6309016849083957064637579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206011232722638043091719 6309016849083957064637579)
    ·
      refine ⟨9463525273625935596956369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309016849083957064637579 9463525273625935596956369)
      ·
        refine ⟨7097643955219451697717277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9463525273625935596956369 7097643955219451697717277)
        ·
          refine ⟨2661616483207294386643979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7097643955219451697717277 2661616483207294386643979)
          ·
            refine ⟨3992424724810941579965969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661616483207294386643979 3992424724810941579965969)
            ·
              refine ⟨2994318543608206184974477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3992424724810941579965969 2994318543608206184974477)
              ·
                refine ⟨1122869453853077319365429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994318543608206184974477 1122869453853077319365429)
                ·
                  refine ⟨105269011298725998690509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122869453853077319365429 105269011298725998690509)
                  ·
                    rfl

theorem cell21_461274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_461274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461274 prefixEnd_461274 := by exact prefixLift 461274
  have htrace : WordTrace (prefixWord ++ tailWord_461274) baseStart_461274 baseEnd_461274 := by
    simpa [prefixWord, tailWord_461274, baseEnd_461274] using wordTrace_append hprefix tailTrace_461274
  have hstable : (prefixWord ++ tailWord_461274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461274).length < 2 ^ (prefixWord ++ tailWord_461274).sum := by decide
  have hdescent : baseEnd_461274 < baseStart_461274 := by decide
  rcases family_descends (prefixWord ++ tailWord_461274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461325 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 5]
def baseStart_461325 : Nat := 118140960795 + 461325 * 2 ^ 59
def prefixEnd_461325 : Nat := 4983230072969 + 3 ^ 40 * 461325 * 2
def baseEnd_461325 : Nat := 105280650193561243340405

theorem tailTrace_461325 : CollatzResearch.WordTrace tailWord_461325 prefixEnd_461325 105280650193561243340405 := by
  unfold tailWord_461325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825905053705787882473429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11217270035803858588315619 16825905053705787882473429)
  ·
    refine ⟨394357149696229403495471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16825905053705787882473429 394357149696229403495471)
    ·
      refine ⟨591535724544344105243207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394357149696229403495471 591535724544344105243207)
      ·
        refine ⟨887303586816516157864811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591535724544344105243207 887303586816516157864811)
        ·
          refine ⟨1330955380224774236797217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887303586816516157864811 1330955380224774236797217)
          ·
            refine ⟨998216535168580677597913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330955380224774236797217 998216535168580677597913)
            ·
              refine ⟨748662401376435508198435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998216535168580677597913 748662401376435508198435)
              ·
                refine ⟨1122993602064653262297653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748662401376435508198435 1122993602064653262297653)
                ·
                  refine ⟨105280650193561243340405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122993602064653262297653 105280650193561243340405)
                  ·
                    rfl

theorem cell21_461325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_461325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461325 prefixEnd_461325 := by exact prefixLift 461325
  have htrace : WordTrace (prefixWord ++ tailWord_461325) baseStart_461325 baseEnd_461325 := by
    simpa [prefixWord, tailWord_461325, baseEnd_461325] using wordTrace_append hprefix tailTrace_461325
  have hstable : (prefixWord ++ tailWord_461325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461325).length < 2 ^ (prefixWord ++ tailWord_461325).sum := by decide
  have hdescent : baseEnd_461325 < baseStart_461325 := by decide
  rcases family_descends (prefixWord ++ tailWord_461325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461522 : List Nat := [3, 2, 2, 2, 4, 1, 2, 5]
def baseStart_461522 : Nat := 118140960795 + 461522 * 2 ^ 59
def prefixEnd_461522 : Nat := 4983230072969 + 3 ^ 40 * 461522 * 2
def baseEnd_461522 : Nat := 35108536092510892852223

theorem tailTrace_461522 : CollatzResearch.WordTrace tailWord_461522 prefixEnd_461522 35108536092510892852223 := by
  unfold tailWord_461522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208272558498022631848705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11222060155994727018263213 4208272558498022631848705)
  ·
    refine ⟨3156204418873516973886529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4208272558498022631848705 3156204418873516973886529)
    ·
      refine ⟨2367153314155137730414897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3156204418873516973886529 2367153314155137730414897)
      ·
        refine ⟨1775364985616353297811173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367153314155137730414897 1775364985616353297811173)
        ·
          refine ⟨332880934803066243339595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1775364985616353297811173 332880934803066243339595)
          ·
            refine ⟨499321402204599365009393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332880934803066243339595 499321402204599365009393)
            ·
              refine ⟨374491051653449523757045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499321402204599365009393 374491051653449523757045)
              ·
                refine ⟨35108536092510892852223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374491051653449523757045 35108536092510892852223)
                ·
                  rfl

theorem cell21_461522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_461522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461522 prefixEnd_461522 := by exact prefixLift 461522
  have htrace : WordTrace (prefixWord ++ tailWord_461522) baseStart_461522 baseEnd_461522 := by
    simpa [prefixWord, tailWord_461522, baseEnd_461522] using wordTrace_append hprefix tailTrace_461522
  have hstable : (prefixWord ++ tailWord_461522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461522).length < 2 ^ (prefixWord ++ tailWord_461522).sum := by decide
  have hdescent : baseEnd_461522 < baseStart_461522 := by decide
  rcases family_descends (prefixWord ++ tailWord_461522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461671 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 3]
def baseStart_461671 : Nat := 118140960795 + 461671 * 2 ^ 59
def prefixEnd_461671 : Nat := 4983230072969 + 3 ^ 40 * 461671 * 2
def baseEnd_461671 : Nat := 105359612107541530573031

theorem tailTrace_461671 : CollatzResearch.WordTrace tailWord_461671 prefixEnd_461671 105359612107541530573031 := by
  unfold tailWord_461671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16838524710452288974568867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11225683140301525983045911 16838524710452288974568867)
  ·
    refine ⟨25257787065678433461853301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16838524710452288974568867 25257787065678433461853301)
    ·
      refine ⟨2367917537407353137048747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25257787065678433461853301 2367917537407353137048747)
      ·
        refine ⟨3551876306111029705573121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367917537407353137048747 3551876306111029705573121)
        ·
          refine ⟨2663907229583272279179841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3551876306111029705573121 2663907229583272279179841)
          ·
            refine ⟨1997930422187454209384881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663907229583272279179841 1997930422187454209384881)
            ·
              refine ⟨1498447816640590657038661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997930422187454209384881 1498447816640590657038661)
              ·
                refine ⟨280958965620110748194749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1498447816640590657038661 280958965620110748194749)
                ·
                  refine ⟨105359612107541530573031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280958965620110748194749 105359612107541530573031)
                  ·
                    rfl

theorem cell21_461671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].length) (baseStart_461671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461671 prefixEnd_461671 := by exact prefixLift 461671
  have htrace : WordTrace (prefixWord ++ tailWord_461671) baseStart_461671 baseEnd_461671 := by
    simpa [prefixWord, tailWord_461671, baseEnd_461671] using wordTrace_append hprefix tailTrace_461671
  have hstable : (prefixWord ++ tailWord_461671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461671).length < 2 ^ (prefixWord ++ tailWord_461671).sum := by decide
  have hdescent : baseEnd_461671 < baseStart_461671 := by decide
  rcases family_descends (prefixWord ++ tailWord_461671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461778 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_461778 : Nat := 118140960795 + 461778 * 2 ^ 59
def prefixEnd_461778 : Nat := 4983230072969 + 3 ^ 40 * 461778 * 2
def baseEnd_461778 : Nat := 105384030965333122289479

theorem tailTrace_461778 : CollatzResearch.WordTrace tailWord_461778 prefixEnd_461778 105384030965333122289479 := by
  unfold tailWord_461778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210606830266161562178497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11228284880709764165809325 4210606830266161562178497)
  ·
    refine ⟨3157955122699621171633873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210606830266161562178497 3157955122699621171633873)
    ·
      refine ⟨2368466342024715878725405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157955122699621171633873 2368466342024715878725405)
      ·
        refine ⟨888174878259268454522027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2368466342024715878725405 888174878259268454522027)
        ·
          refine ⟨1332262317388902681783041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888174878259268454522027 1332262317388902681783041)
          ·
            refine ⟨999196738041677011337281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332262317388902681783041 999196738041677011337281)
            ·
              refine ⟨749397553531257758502961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999196738041677011337281 749397553531257758502961)
              ·
                refine ⟨562048165148443318877221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749397553531257758502961 562048165148443318877221)
                ·
                  refine ⟨105384030965333122289479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562048165148443318877221 105384030965333122289479)
                  ·
                    rfl

theorem cell21_461778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_461778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461778 prefixEnd_461778 := by exact prefixLift 461778
  have htrace : WordTrace (prefixWord ++ tailWord_461778) baseStart_461778 baseEnd_461778 := by
    simpa [prefixWord, tailWord_461778, baseEnd_461778] using wordTrace_append hprefix tailTrace_461778
  have hstable : (prefixWord ++ tailWord_461778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461778).length < 2 ^ (prefixWord ++ tailWord_461778).sum := by decide
  have hdescent : baseEnd_461778 < baseStart_461778 := by decide
  rcases family_descends (prefixWord ++ tailWord_461778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461781 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 3]
def baseStart_461781 : Nat := 118140960795 + 461781 * 2 ^ 59
def prefixEnd_461781 : Nat := 4983230072969 + 3 ^ 40 * 461781 * 2
def baseEnd_461781 : Nat := 105384715606205783739473

theorem tailTrace_461781 : CollatzResearch.WordTrace tailWord_461781 prefixEnd_461781 105384715606205783739473 := by
  unfold tailWord_461781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842536740053777761073197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11228357826702518507382131 16842536740053777761073197)
  ·
    refine ⟨6315951277520166660402449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16842536740053777761073197 6315951277520166660402449)
    ·
      refine ⟨4736963458140124995301837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6315951277520166660402449 4736963458140124995301837)
      ·
        refine ⟨1776361296802546873238189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4736963458140124995301837 1776361296802546873238189)
        ·
          refine ⟨666135486300955077464321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776361296802546873238189 666135486300955077464321)
          ·
            refine ⟨499601614725716308098241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666135486300955077464321 499601614725716308098241)
            ·
              refine ⟨374701211044287231073681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499601614725716308098241 374701211044287231073681)
              ·
                refine ⟨281025908283215423305261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374701211044287231073681 281025908283215423305261)
                ·
                  refine ⟨105384715606205783739473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281025908283215423305261 105384715606205783739473)
                  ·
                    rfl

theorem cell21_461781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_461781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461781 prefixEnd_461781 := by exact prefixLift 461781
  have htrace : WordTrace (prefixWord ++ tailWord_461781) baseStart_461781 baseEnd_461781 := by
    simpa [prefixWord, tailWord_461781, baseEnd_461781] using wordTrace_append hprefix tailTrace_461781
  have hstable : (prefixWord ++ tailWord_461781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461781).length < 2 ^ (prefixWord ++ tailWord_461781).sum := by decide
  have hdescent : baseEnd_461781 < baseStart_461781 := by decide
  rcases family_descends (prefixWord ++ tailWord_461781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461803 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_461803 : Nat := 118140960795 + 461803 * 2 ^ 59
def prefixEnd_461803 : Nat := 4983230072969 + 3 ^ 40 * 461803 * 2
def baseEnd_461803 : Nat := 105389736305938634372761

theorem tailTrace_461803 : CollatzResearch.WordTrace tailWord_461803 prefixEnd_461803 105389736305938634372761 := by
  unfold tailWord_461803
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843339145974075518374063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11228892763982717012249375 16843339145974075518374063)
  ·
    refine ⟨25265008718961113277561095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16843339145974075518374063 25265008718961113277561095)
    ·
      refine ⟨37897513078441669916341643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25265008718961113277561095 37897513078441669916341643)
      ·
        refine ⟨56846269617662504874512465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37897513078441669916341643 56846269617662504874512465)
        ·
          refine ⟨42634702213246878655884349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56846269617662504874512465 42634702213246878655884349)
          ·
            refine ⟨15988013329967579495956631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42634702213246878655884349 15988013329967579495956631)
            ·
              refine ⟨23982019994951369243934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15988013329967579495956631 23982019994951369243934947)
              ·
                refine ⟨35973029992427053865902421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23982019994951369243934947 35973029992427053865902421)
                ·
                  refine ⟨105389736305938634372761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35973029992427053865902421 105389736305938634372761)
                  ·
                    rfl

theorem cell21_461803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_461803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461803 prefixEnd_461803 := by exact prefixLift 461803
  have htrace : WordTrace (prefixWord ++ tailWord_461803) baseStart_461803 baseEnd_461803 := by
    simpa [prefixWord, tailWord_461803, baseEnd_461803] using wordTrace_append hprefix tailTrace_461803
  have hstable : (prefixWord ++ tailWord_461803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461803).length < 2 ^ (prefixWord ++ tailWord_461803).sum := by decide
  have hdescent : baseEnd_461803 < baseStart_461803 := by decide
  rcases family_descends (prefixWord ++ tailWord_461803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461896 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_461896 : Nat := 118140960795 + 461896 * 2 ^ 59
def prefixEnd_461896 : Nat := 4983230072969 + 3 ^ 40 * 461896 * 2
def baseEnd_461896 : Nat := 105410960172991139322571

theorem tailTrace_461896 : CollatzResearch.WordTrace tailWord_461896 prefixEnd_461896 105410960172991139322571 := by
  unfold tailWord_461896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423365567318576200754771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11231154089758101601006361 8423365567318576200754771)
  ·
    refine ⟨12635048350977864301132157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8423365567318576200754771 12635048350977864301132157)
    ·
      refine ⟨4738143131616699112924559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12635048350977864301132157 4738143131616699112924559)
      ·
        refine ⟨7107214697425048669386839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738143131616699112924559 7107214697425048669386839)
        ·
          refine ⟨10660822046137573004080259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107214697425048669386839 10660822046137573004080259)
          ·
            refine ⟨15991233069206359506120389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660822046137573004080259 15991233069206359506120389)
            ·
              refine ⟨2998356200476192407397573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15991233069206359506120389 2998356200476192407397573)
              ·
                refine ⟨562191787589286076387045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2998356200476192407397573 562191787589286076387045)
                ·
                  refine ⟨105410960172991139322571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562191787589286076387045 105410960172991139322571)
                  ·
                    rfl

theorem cell21_461896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_461896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461896 prefixEnd_461896 := by exact prefixLift 461896
  have htrace : WordTrace (prefixWord ++ tailWord_461896) baseStart_461896 baseEnd_461896 := by
    simpa [prefixWord, tailWord_461896, baseEnd_461896] using wordTrace_append hprefix tailTrace_461896
  have hstable : (prefixWord ++ tailWord_461896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461896).length < 2 ^ (prefixWord ++ tailWord_461896).sum := by decide
  have hdescent : baseEnd_461896 < baseStart_461896 := by decide
  rcases family_descends (prefixWord ++ tailWord_461896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461950 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_461950 : Nat := 118140960795 + 461950 * 2 ^ 59
def prefixEnd_461950 : Nat := 4983230072969 + 3 ^ 40 * 461950 * 2
def baseEnd_461950 : Nat := 105423283708699045422461

theorem tailTrace_461950 : CollatzResearch.WordTrace tailWord_461950 prefixEnd_461950 105423283708699045422461 := by
  unfold tailWord_461950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106087584555189952996913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11232467117627679749316869 2106087584555189952996913)
  ·
    refine ⟨1579565688416392464747685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106087584555189952996913 1579565688416392464747685)
    ·
      refine ⟨296168566578073587140191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1579565688416392464747685 296168566578073587140191)
      ·
        refine ⟨444252849867110380710287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296168566578073587140191 444252849867110380710287)
        ·
          refine ⟨666379274800665571065431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444252849867110380710287 666379274800665571065431)
          ·
            refine ⟨999568912200998356598147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666379274800665571065431 999568912200998356598147)
            ·
              refine ⟨1499353368301497534897221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999568912200998356598147 1499353368301497534897221)
              ·
                refine ⟨281128756556530787793229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1499353368301497534897221 281128756556530787793229)
                ·
                  refine ⟨105423283708699045422461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281128756556530787793229 105423283708699045422461)
                  ·
                    rfl

theorem cell21_461950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_461950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_461950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_461950 prefixEnd_461950 := by exact prefixLift 461950
  have htrace : WordTrace (prefixWord ++ tailWord_461950) baseStart_461950 baseEnd_461950 := by
    simpa [prefixWord, tailWord_461950, baseEnd_461950] using wordTrace_append hprefix tailTrace_461950
  have hstable : (prefixWord ++ tailWord_461950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461950).length < 2 ^ (prefixWord ++ tailWord_461950).sum := by decide
  have hdescent : baseEnd_461950 < baseStart_461950 := by decide
  rcases family_descends (prefixWord ++ tailWord_461950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462062 : List Nat := [4, 1, 2, 1, 1, 1, 11]
def baseStart_462062 : Nat := 118140960795 + 462062 * 2 ^ 59
def prefixEnd_462062 : Nat := 4983230072969 + 3 ^ 40 * 462062 * 2
def baseEnd_462062 : Nat := 11716538181623526617285

theorem tailTrace_462062 : CollatzResearch.WordTrace tailWord_462062 prefixEnd_462062 11716538181623526617285 := by
  unfold tailWord_462062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106598206504470344006555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11235190434690508501368293 2106598206504470344006555)
  ·
    refine ⟨3159897309756705516009833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2106598206504470344006555 3159897309756705516009833)
    ·
      refine ⟨2369922982317529137007375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3159897309756705516009833 2369922982317529137007375)
      ·
        refine ⟨3554884473476293705511063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369922982317529137007375 3554884473476293705511063)
        ·
          refine ⟨5332326710214440558266595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554884473476293705511063 5332326710214440558266595)
          ·
            refine ⟨7998490065321660837399893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332326710214440558266595 7998490065321660837399893)
            ·
              refine ⟨11716538181623526617285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7998490065321660837399893 11716538181623526617285)
              ·
                rfl

theorem cell21_462062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 11].length) (baseStart_462062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462062 prefixEnd_462062 := by exact prefixLift 462062
  have htrace : WordTrace (prefixWord ++ tailWord_462062) baseStart_462062 baseEnd_462062 := by
    simpa [prefixWord, tailWord_462062, baseEnd_462062] using wordTrace_append hprefix tailTrace_462062
  have hstable : (prefixWord ++ tailWord_462062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462062).length < 2 ^ (prefixWord ++ tailWord_462062).sum := by decide
  have hdescent : baseEnd_462062 < baseStart_462062 := by decide
  rcases family_descends (prefixWord ++ tailWord_462062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462082 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_462082 : Nat := 118140960795 + 462082 * 2 ^ 59
def prefixEnd_462082 : Nat := 4983230072969 + 3 ^ 40 * 462082 * 2
def baseEnd_462082 : Nat := 105453407907096149222191

theorem tailTrace_462082 : CollatzResearch.WordTrace tailWord_462082 prefixEnd_462082 105453407907096149222191 := by
  unfold tailWord_462082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213378777990826541945125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11235676741308870778520333 4213378777990826541945125)
  ·
    refine ⟨790008520873279976614711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4213378777990826541945125 790008520873279976614711)
    ·
      refine ⟨1185012781309919964922067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790008520873279976614711 1185012781309919964922067)
      ·
        refine ⟨1777519171964879947383101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185012781309919964922067 1777519171964879947383101)
        ·
          refine ⟨666569689486829980268663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1777519171964879947383101 666569689486829980268663)
          ·
            refine ⟨999854534230244970402995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666569689486829980268663 999854534230244970402995)
            ·
              refine ⟨1499781801345367455604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999854534230244970402995 1499781801345367455604493)
              ·
                refine ⟨562418175504512795851685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499781801345367455604493 562418175504512795851685)
                ·
                  refine ⟨105453407907096149222191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562418175504512795851685 105453407907096149222191)
                  ·
                    rfl

theorem cell21_462082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_462082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462082 prefixEnd_462082 := by exact prefixLift 462082
  have htrace : WordTrace (prefixWord ++ tailWord_462082) baseStart_462082 baseEnd_462082 := by
    simpa [prefixWord, tailWord_462082, baseEnd_462082] using wordTrace_append hprefix tailTrace_462082
  have hstable : (prefixWord ++ tailWord_462082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462082).length < 2 ^ (prefixWord ++ tailWord_462082).sum := by decide
  have hdescent : baseEnd_462082 < baseStart_462082 := by decide
  rcases family_descends (prefixWord ++ tailWord_462082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462206 : List Nat := [4, 2, 3, 2, 1, 2, 2, 5]
def baseStart_462206 : Nat := 118140960795 + 462206 * 2 ^ 59
def prefixEnd_462206 : Nat := 4983230072969 + 3 ^ 40 * 462206 * 2
def baseEnd_462206 : Nat := 35160568798833163051757

theorem tailTrace_462206 : CollatzResearch.WordTrace tailWord_462206 prefixEnd_462206 35160568798833163051757 := by
  unfold tailWord_462206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107254720439259418161809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11238691842342716896862981 2107254720439259418161809)
  ·
    refine ⟨1580441040329444563621357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2107254720439259418161809 1580441040329444563621357)
    ·
      refine ⟨592665390123541711358009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1580441040329444563621357 592665390123541711358009)
      ·
        refine ⟨444499042592656283518507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592665390123541711358009 444499042592656283518507)
        ·
          refine ⟨666748563888984425277761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444499042592656283518507 666748563888984425277761)
          ·
            refine ⟨500061422916738318958321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666748563888984425277761 500061422916738318958321)
            ·
              refine ⟨375046067187553739218741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500061422916738318958321 375046067187553739218741)
              ·
                refine ⟨35160568798833163051757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375046067187553739218741 35160568798833163051757)
                ·
                  rfl

theorem cell21_462206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_462206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462206 prefixEnd_462206 := by exact prefixLift 462206
  have htrace : WordTrace (prefixWord ++ tailWord_462206) baseStart_462206 baseEnd_462206 := by
    simpa [prefixWord, tailWord_462206, baseEnd_462206] using wordTrace_append hprefix tailTrace_462206
  have hstable : (prefixWord ++ tailWord_462206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462206).length < 2 ^ (prefixWord ++ tailWord_462206).sum := by decide
  have hdescent : baseEnd_462206 < baseStart_462206 := by decide
  rcases family_descends (prefixWord ++ tailWord_462206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462248 : List Nat := [2, 1, 6, 1, 2, 1, 2, 6]
def baseStart_462248 : Nat := 118140960795 + 462248 * 2 ^ 59
def prefixEnd_462248 : Nat := 4983230072969 + 3 ^ 40 * 462248 * 2
def baseEnd_462248 : Nat := 35163763789572249818395

theorem tailTrace_462248 : CollatzResearch.WordTrace tailWord_462248 prefixEnd_462248 35163763789572249818395 := by
  unfold tailWord_462248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429784814680958259161699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11239713086241277678882265 8429784814680958259161699)
  ·
    refine ⟨12644677222021437388742549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429784814680958259161699 12644677222021437388742549)
    ·
      refine ⟨592719244782254877597307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12644677222021437388742549 592719244782254877597307)
      ·
        refine ⟨889078867173382316395961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592719244782254877597307 889078867173382316395961)
        ·
          refine ⟨666809150380036737296971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889078867173382316395961 666809150380036737296971)
          ·
            refine ⟨1000213725570055105945457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666809150380036737296971 1000213725570055105945457)
            ·
              refine ⟨750160294177541329459093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000213725570055105945457 750160294177541329459093)
              ·
                refine ⟨35163763789572249818395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 750160294177541329459093 35163763789572249818395)
                ·
                  rfl

theorem cell21_462248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_462248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462248 prefixEnd_462248 := by exact prefixLift 462248
  have htrace : WordTrace (prefixWord ++ tailWord_462248) baseStart_462248 baseEnd_462248 := by
    simpa [prefixWord, tailWord_462248, baseEnd_462248] using wordTrace_append hprefix tailTrace_462248
  have hstable : (prefixWord ++ tailWord_462248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462248).length < 2 ^ (prefixWord ++ tailWord_462248).sum := by decide
  have hdescent : baseEnd_462248 < baseStart_462248 := by decide
  rcases family_descends (prefixWord ++ tailWord_462248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462307 : List Nat := [1, 1, 1, 6, 2, 3, 1, 6]
def baseStart_462307 : Nat := 118140960795 + 462307 * 2 ^ 59
def prefixEnd_462307 : Nat := 4983230072969 + 3 ^ 40 * 462307 * 2
def baseEnd_462307 : Nat := 35168251990848585990577

theorem tailTrace_462307 : CollatzResearch.WordTrace tailWord_462307 prefixEnd_462307 35168251990848585990577 := by
  unfold tailWord_462307
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861721536148169594721175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11241147690765446396480783 16861721536148169594721175)
  ·
    refine ⟨25292582304222254392081763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16861721536148169594721175 25292582304222254392081763)
    ·
      refine ⟨37938873456333381588122645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25292582304222254392081763 37938873456333381588122645)
      ·
        refine ⟨1778384693265627261943249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37938873456333381588122645 1778384693265627261943249)
        ·
          refine ⟨1333788519949220446457437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778384693265627261943249 1333788519949220446457437)
          ·
            refine ⟨500170694980957667421539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1333788519949220446457437 500170694980957667421539)
            ·
              refine ⟨750256042471436501132309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500170694980957667421539 750256042471436501132309)
              ·
                refine ⟨35168251990848585990577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 750256042471436501132309 35168251990848585990577)
                ·
                  rfl

theorem cell21_462307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_462307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462307 prefixEnd_462307 := by exact prefixLift 462307
  have htrace : WordTrace (prefixWord ++ tailWord_462307) baseStart_462307 baseEnd_462307 := by
    simpa [prefixWord, tailWord_462307, baseEnd_462307] using wordTrace_append hprefix tailTrace_462307
  have hstable : (prefixWord ++ tailWord_462307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462307).length < 2 ^ (prefixWord ++ tailWord_462307).sum := by decide
  have hdescent : baseEnd_462307 < baseStart_462307 := by decide
  rcases family_descends (prefixWord ++ tailWord_462307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462321 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_462321 : Nat := 118140960795 + 462321 * 2 ^ 59
def prefixEnd_462321 : Nat := 4983230072969 + 3 ^ 40 * 462321 * 2
def baseEnd_462321 : Nat := 105507950963284844738369

theorem tailTrace_462321 : CollatzResearch.WordTrace tailWord_462321 prefixEnd_462321 105507950963284844738369 := by
  unfold tailWord_462321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862232158097449985730817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11241488105398299990487211 16862232158097449985730817)
  ·
    refine ⟨12646674118573087489298113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16862232158097449985730817 12646674118573087489298113)
    ·
      refine ⟨9485005588929815616973585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12646674118573087489298113 9485005588929815616973585)
      ·
        refine ⟨7113754191697361712730189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9485005588929815616973585 7113754191697361712730189)
        ·
          refine ⟨2667657821886510642273821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7113754191697361712730189 2667657821886510642273821)
          ·
            refine ⟨1000371683207441490852683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667657821886510642273821 1000371683207441490852683)
            ·
              refine ⟨1500557524811162236279025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000371683207441490852683 1500557524811162236279025)
              ·
                refine ⟨1125418143608371677209269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500557524811162236279025 1125418143608371677209269)
                ·
                  refine ⟨105507950963284844738369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125418143608371677209269 105507950963284844738369)
                  ·
                    rfl

theorem cell21_462321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_462321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462321 prefixEnd_462321 := by exact prefixLift 462321
  have htrace : WordTrace (prefixWord ++ tailWord_462321) baseStart_462321 baseEnd_462321 := by
    simpa [prefixWord, tailWord_462321, baseEnd_462321] using wordTrace_append hprefix tailTrace_462321
  have hstable : (prefixWord ++ tailWord_462321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462321).length < 2 ^ (prefixWord ++ tailWord_462321).sum := by decide
  have hdescent : baseEnd_462321 < baseStart_462321 := by decide
  rcases family_descends (prefixWord ++ tailWord_462321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462369 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 4]
def baseStart_462369 : Nat := 118140960795 + 462369 * 2 ^ 59
def prefixEnd_462369 : Nat := 4983230072969 + 3 ^ 40 * 462369 * 2
def baseEnd_462369 : Nat := 105518905217247427938271

theorem tailTrace_462369 : CollatzResearch.WordTrace tailWord_462369 prefixEnd_462369 105518905217247427938271 := by
  unfold tailWord_462369
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863982861923554183478161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11242655241282369455652107 16863982861923554183478161)
  ·
    refine ⟨12647987146442665637608621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16863982861923554183478161 12647987146442665637608621)
    ·
      refine ⟨4742995179915999614103233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12647987146442665637608621 4742995179915999614103233)
      ·
        refine ⟨3557246384936999710577425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4742995179915999614103233 3557246384936999710577425)
        ·
          refine ⟨2667934788702749782933069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557246384936999710577425 2667934788702749782933069)
          ·
            refine ⟨1000475545763531168599901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667934788702749782933069 1000475545763531168599901)
            ·
              refine ⟨375178329661324188224963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000475545763531168599901 375178329661324188224963)
              ·
                refine ⟨562767494491986282337445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375178329661324188224963 562767494491986282337445)
                ·
                  refine ⟨105518905217247427938271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562767494491986282337445 105518905217247427938271)
                  ·
                    rfl

theorem cell21_462369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_462369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462369 prefixEnd_462369 := by exact prefixLift 462369
  have htrace : WordTrace (prefixWord ++ tailWord_462369) baseStart_462369 baseEnd_462369 := by
    simpa [prefixWord, tailWord_462369, baseEnd_462369] using wordTrace_append hprefix tailTrace_462369
  have hstable : (prefixWord ++ tailWord_462369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462369).length < 2 ^ (prefixWord ++ tailWord_462369).sum := by decide
  have hdescent : baseEnd_462369 < baseStart_462369 := by decide
  rcases family_descends (prefixWord ++ tailWord_462369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462411 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_462411 : Nat := 118140960795 + 462411 * 2 ^ 59
def prefixEnd_462411 : Nat := 4983230072969 + 3 ^ 40 * 462411 * 2
def baseEnd_462411 : Nat := 105528490189464688238185

theorem tailTrace_462411 : CollatzResearch.WordTrace tailWord_462411 prefixEnd_462411 105528490189464688238185 := by
  unfold tailWord_462411
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865514727771395356507087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243676485180930237671391 16865514727771395356507087)
  ·
    refine ⟨25298272091657093034760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865514727771395356507087 25298272091657093034760631)
    ·
      refine ⟨37947408137485639552140947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25298272091657093034760631 37947408137485639552140947)
      ·
        refine ⟨56921112206228459328211421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37947408137485639552140947 56921112206228459328211421)
        ·
          refine ⟨21345417077335672248079283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56921112206228459328211421 21345417077335672248079283)
          ·
            refine ⟨32018125616003508372118925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345417077335672248079283 32018125616003508372118925)
            ·
              refine ⟨12006797106001315639544597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32018125616003508372118925 12006797106001315639544597)
              ·
                refine ⟨562818614343811670603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12006797106001315639544597 562818614343811670603653)
                ·
                  refine ⟨105528490189464688238185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562818614343811670603653 105528490189464688238185)
                  ·
                    rfl

theorem cell21_462411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_462411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462411 prefixEnd_462411 := by exact prefixLift 462411
  have htrace : WordTrace (prefixWord ++ tailWord_462411) baseStart_462411 baseEnd_462411 := by
    simpa [prefixWord, tailWord_462411, baseEnd_462411] using wordTrace_append hprefix tailTrace_462411
  have hstable : (prefixWord ++ tailWord_462411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462411).length < 2 ^ (prefixWord ++ tailWord_462411).sum := by decide
  have hdescent : baseEnd_462411 < baseStart_462411 := by decide
  rcases family_descends (prefixWord ++ tailWord_462411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462442 : List Nat := [3, 1, 3, 2, 1, 2, 2, 7]
def baseStart_462442 : Nat := 118140960795 + 462442 * 2 ^ 59
def prefixEnd_462442 : Nat := 4983230072969 + 3 ^ 40 * 462442 * 2
def baseEnd_462442 : Nat := 35178521603938507740485

theorem tailTrace_462442 : CollatzResearch.WordTrace tailWord_462442 prefixEnd_462442 35178521603938507740485 := by
  unfold tailWord_462442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216661347664771912721395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11244430260439391767257053 4216661347664771912721395)
  ·
    refine ⟨6324992021497157869082093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4216661347664771912721395 6324992021497157869082093)
    ·
      refine ⟨2371872008061434200905785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6324992021497157869082093 2371872008061434200905785)
      ·
        refine ⟨1778904006046075650679339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2371872008061434200905785 1778904006046075650679339)
        ·
          refine ⟨2668356009069113476019009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778904006046075650679339 2668356009069113476019009)
          ·
            refine ⟨2001267006801835107014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668356009069113476019009 2001267006801835107014257)
            ·
              refine ⟨1500950255101376330260693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001267006801835107014257 1500950255101376330260693)
              ·
                refine ⟨35178521603938507740485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1500950255101376330260693 35178521603938507740485)
                ·
                  rfl

theorem cell21_462442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_462442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462442 prefixEnd_462442 := by exact prefixLift 462442
  have htrace : WordTrace (prefixWord ++ tailWord_462442) baseStart_462442 baseEnd_462442 := by
    simpa [prefixWord, tailWord_462442, baseEnd_462442] using wordTrace_append hprefix tailTrace_462442
  have hstable : (prefixWord ++ tailWord_462442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462442).length < 2 ^ (prefixWord ++ tailWord_462442).sum := by decide
  have hdescent : baseEnd_462442 < baseStart_462442 := by decide
  rcases family_descends (prefixWord ++ tailWord_462442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462501 : List Nat := [1, 3, 1, 2, 1, 2, 2, 9]
def baseStart_462501 : Nat := 118140960795 + 462501 * 2 ^ 59
def prefixEnd_462501 : Nat := 4983230072969 + 3 ^ 40 * 462501 * 2
def baseEnd_462501 : Nat := 35183009805214843912667

theorem tailTrace_462501 : CollatzResearch.WordTrace tailWord_462501 prefixEnd_462501 35183009805214843912667 := by
  unfold tailWord_462501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868797297445340727283357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245864864963560484855571 16868797297445340727283357)
  ·
    refine ⟨6325798986542002772731259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16868797297445340727283357 6325798986542002772731259)
    ·
      refine ⟨9488698479813004159096889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325798986542002772731259 9488698479813004159096889)
      ·
        refine ⟨7116523859859753119322667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9488698479813004159096889 7116523859859753119322667)
        ·
          refine ⟨10674785789789629678984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116523859859753119322667 10674785789789629678984001)
          ·
            refine ⟨8006089342342222259238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10674785789789629678984001 8006089342342222259238001)
            ·
              refine ⟨6004567006756666694428501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006089342342222259238001 6004567006756666694428501)
              ·
                refine ⟨35183009805214843912667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6004567006756666694428501 35183009805214843912667)
                ·
                  rfl

theorem cell21_462501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_462501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462501 prefixEnd_462501 := by exact prefixLift 462501
  have htrace : WordTrace (prefixWord ++ tailWord_462501) baseStart_462501 baseEnd_462501 := by
    simpa [prefixWord, tailWord_462501, baseEnd_462501] using wordTrace_append hprefix tailTrace_462501
  have hstable : (prefixWord ++ tailWord_462501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462501).length < 2 ^ (prefixWord ++ tailWord_462501).sum := by decide
  have hdescent : baseEnd_462501 < baseStart_462501 := by decide
  rcases family_descends (prefixWord ++ tailWord_462501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462577 : List Nat := [1, 2, 2, 2, 2, 3, 9]
def baseStart_462577 : Nat := 118140960795 + 462577 * 2 ^ 59
def prefixEnd_462577 : Nat := 4983230072969 + 3 ^ 40 * 462577 * 2
def baseEnd_462577 : Nat := 11729597072342809830131

theorem tailTrace_462577 : CollatzResearch.WordTrace tailWord_462577 prefixEnd_462577 11729597072342809830131 := by
  unfold tailWord_462577
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871569245170005707049985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11247712830113337138033323 16871569245170005707049985)
  ·
    refine ⟨12653676933877504280287489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16871569245170005707049985 12653676933877504280287489)
    ·
      refine ⟨9490257700408128210215617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12653676933877504280287489 9490257700408128210215617)
      ·
        refine ⟨7117693275306096157661713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490257700408128210215617 7117693275306096157661713)
        ·
          refine ⟨5338269956479572118246285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7117693275306096157661713 5338269956479572118246285)
          ·
            refine ⟨2001851233679839544342357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5338269956479572118246285 2001851233679839544342357)
            ·
              refine ⟨11729597072342809830131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2001851233679839544342357 11729597072342809830131)
              ·
                rfl

theorem cell21_462577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 9].length) (baseStart_462577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462577 prefixEnd_462577 := by exact prefixLift 462577
  have htrace : WordTrace (prefixWord ++ tailWord_462577) baseStart_462577 baseEnd_462577 := by
    simpa [prefixWord, tailWord_462577, baseEnd_462577] using wordTrace_append hprefix tailTrace_462577
  have hstable : (prefixWord ++ tailWord_462577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462577).length < 2 ^ (prefixWord ++ tailWord_462577).sum := by decide
  have hdescent : baseEnd_462577 < baseStart_462577 := by decide
  rcases family_descends (prefixWord ++ tailWord_462577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462642 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_462642 : Nat := 118140960795 + 462642 * 2 ^ 59
def prefixEnd_462642 : Nat := 4983230072969 + 3 ^ 40 * 462642 * 2
def baseEnd_462642 : Nat := 105581207536659619887713

theorem tailTrace_462642 : CollatzResearch.WordTrace tailWord_462642 prefixEnd_462642 105581207536659619887713 := by
  unfold tailWord_462642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218484997483630452041545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11249293326623014538777453 4218484997483630452041545)
  ·
    refine ⟨3163863748112722839031159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4218484997483630452041545 3163863748112722839031159)
    ·
      refine ⟨4745795622169084258546739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163863748112722839031159 4745795622169084258546739)
      ·
        refine ⟨7118693433253626387820109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745795622169084258546739 7118693433253626387820109)
        ·
          refine ⟨2669510037470109895432541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7118693433253626387820109 2669510037470109895432541)
          ·
            refine ⟨1001066264051291210787203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2669510037470109895432541 1001066264051291210787203)
            ·
              refine ⟨1501599396076936816180805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001066264051291210787203 1501599396076936816180805)
              ·
                refine ⟨281549886764425653033901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1501599396076936816180805 281549886764425653033901)
                ·
                  refine ⟨105581207536659619887713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281549886764425653033901 105581207536659619887713)
                  ·
                    rfl

theorem cell21_462642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_462642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462642 prefixEnd_462642 := by exact prefixLift 462642
  have htrace : WordTrace (prefixWord ++ tailWord_462642) baseStart_462642 baseEnd_462642 := by
    simpa [prefixWord, tailWord_462642, baseEnd_462642] using wordTrace_append hprefix tailTrace_462642
  have hstable : (prefixWord ++ tailWord_462642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462642).length < 2 ^ (prefixWord ++ tailWord_462642).sum := by decide
  have hdescent : baseEnd_462642 < baseStart_462642 := by decide
  rcases family_descends (prefixWord ++ tailWord_462642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462718 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_462718 : Nat := 118140960795 + 462718 * 2 ^ 59
def prefixEnd_462718 : Nat := 4983230072969 + 3 ^ 40 * 462718 * 2
def baseEnd_462718 : Nat := 105598551772100376620891

theorem tailTrace_462718 : CollatzResearch.WordTrace tailWord_462718 prefixEnd_462718 105598551772100376620891 := by
  unfold tailWord_462718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109588992207398348491601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11251141291772791191955205 2109588992207398348491601)
  ·
    refine ⟨1582191744155548761368701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2109588992207398348491601 1582191744155548761368701)
    ·
      refine ⟨593321904058330785513263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1582191744155548761368701 593321904058330785513263)
      ·
        refine ⟨889982856087496178269895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593321904058330785513263 889982856087496178269895)
        ·
          refine ⟨1334974284131244267404843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889982856087496178269895 1334974284131244267404843)
          ·
            refine ⟨2002461426196866401107265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334974284131244267404843 2002461426196866401107265)
            ·
              refine ⟨1501846069647649800830449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002461426196866401107265 1501846069647649800830449)
              ·
                refine ⟨1126384552235737350622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501846069647649800830449 1126384552235737350622837)
                ·
                  refine ⟨105598551772100376620891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126384552235737350622837 105598551772100376620891)
                  ·
                    rfl

theorem cell21_462718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_462718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462718 prefixEnd_462718 := by exact prefixLift 462718
  have htrace : WordTrace (prefixWord ++ tailWord_462718) baseStart_462718 baseEnd_462718 := by
    simpa [prefixWord, tailWord_462718, baseEnd_462718] using wordTrace_append hprefix tailTrace_462718
  have hstable : (prefixWord ++ tailWord_462718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462718).length < 2 ^ (prefixWord ++ tailWord_462718).sum := by decide
  have hdescent : baseEnd_462718 < baseStart_462718 := by decide
  rcases family_descends (prefixWord ++ tailWord_462718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462721 : List Nat := [1, 2, 4, 4, 2, 1, 2, 5]
def baseStart_462721 : Nat := 118140960795 + 462721 * 2 ^ 59
def prefixEnd_462721 : Nat := 4983230072969 + 3 ^ 40 * 462721 * 2
def baseEnd_462721 : Nat := 35199745470991012690295

theorem tailTrace_462721 : CollatzResearch.WordTrace tailWord_462721 prefixEnd_462721 35199745470991012690295 := by
  unfold tailWord_462721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876821356648318300292017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11251214237765545533528011 16876821356648318300292017)
  ·
    refine ⟨12657616017486238725219013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16876821356648318300292017 12657616017486238725219013)
    ·
      refine ⟨2373303003278669760978565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12657616017486238725219013 2373303003278669760978565)
      ·
        refine ⟨444994313114750580183481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2373303003278669760978565 444994313114750580183481)
        ·
          refine ⟨333745734836062935137611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444994313114750580183481 333745734836062935137611)
          ·
            refine ⟨500618602254094402706417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333745734836062935137611 500618602254094402706417)
            ·
              refine ⟨375463951690570802029813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500618602254094402706417 375463951690570802029813)
              ·
                refine ⟨35199745470991012690295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375463951690570802029813 35199745470991012690295)
                ·
                  rfl

theorem cell21_462721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].length) (baseStart_462721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462721 prefixEnd_462721 := by exact prefixLift 462721
  have htrace : WordTrace (prefixWord ++ tailWord_462721) baseStart_462721 baseEnd_462721 := by
    simpa [prefixWord, tailWord_462721, baseEnd_462721] using wordTrace_append hprefix tailTrace_462721
  have hstable : (prefixWord ++ tailWord_462721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462721).length < 2 ^ (prefixWord ++ tailWord_462721).sum := by decide
  have hdescent : baseEnd_462721 < baseStart_462721 := by decide
  rcases family_descends (prefixWord ++ tailWord_462721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462729 : List Nat := [1, 2, 1, 1, 5, 1, 3, 7]
def baseStart_462729 : Nat := 118140960795 + 462729 * 2 ^ 59
def prefixEnd_462729 : Nat := 4983230072969 + 3 ^ 40 * 462729 * 2
def baseEnd_462729 : Nat := 35200354040655600645845

theorem tailTrace_462729 : CollatzResearch.WordTrace tailWord_462729 prefixEnd_462729 35200354040655600645845 := by
  unfold tailWord_462729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877113140619335666583241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11251408760412890444388827 16877113140619335666583241)
  ·
    refine ⟨12657834855464501749937431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16877113140619335666583241 12657834855464501749937431)
    ·
      refine ⟨18986752283196752624906147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657834855464501749937431 18986752283196752624906147)
      ·
        refine ⟨28480128424795128937359221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18986752283196752624906147 28480128424795128937359221)
        ·
          refine ⟨2670012039824543337877427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28480128424795128937359221 2670012039824543337877427)
          ·
            refine ⟨4005018059736815006816141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670012039824543337877427 4005018059736815006816141)
            ·
              refine ⟨1501881772401305627556053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4005018059736815006816141 1501881772401305627556053)
              ·
                refine ⟨35200354040655600645845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1501881772401305627556053 35200354040655600645845)
                ·
                  rfl

theorem cell21_462729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_462729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462729 prefixEnd_462729 := by exact prefixLift 462729
  have htrace : WordTrace (prefixWord ++ tailWord_462729) baseStart_462729 baseEnd_462729 := by
    simpa [prefixWord, tailWord_462729, baseEnd_462729] using wordTrace_append hprefix tailTrace_462729
  have hstable : (prefixWord ++ tailWord_462729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462729).length < 2 ^ (prefixWord ++ tailWord_462729).sum := by decide
  have hdescent : baseEnd_462729 < baseStart_462729 := by decide
  rcases family_descends (prefixWord ++ tailWord_462729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462746 : List Nat := [3, 1, 1, 4, 2, 3, 7]
def baseStart_462746 : Nat := 118140960795 + 462746 * 2 ^ 59
def prefixEnd_462746 : Nat := 4983230072969 + 3 ^ 40 * 462746 * 2
def baseEnd_462746 : Nat := 11733882417064283350463

theorem tailTrace_462746 : CollatzResearch.WordTrace tailWord_462746 prefixEnd_462746 11733882417064283350463 := by
  unfold tailWord_462746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219433295389436892488023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11251822121038498379968061 4219433295389436892488023)
  ·
    refine ⟨6329149943084155338732035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219433295389436892488023 6329149943084155338732035)
    ·
      refine ⟨9493724914626233008098053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6329149943084155338732035 9493724914626233008098053)
      ·
        refine ⟨1780073421492418689018385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9493724914626233008098053 1780073421492418689018385)
        ·
          refine ⟨1335055066119314016763789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780073421492418689018385 1335055066119314016763789)
          ·
            refine ⟨500645649794742756286421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1335055066119314016763789 500645649794742756286421)
            ·
              refine ⟨11733882417064283350463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 500645649794742756286421 11733882417064283350463)
              ·
                rfl

theorem cell21_462746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 7].length) (baseStart_462746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462746 prefixEnd_462746 := by exact prefixLift 462746
  have htrace : WordTrace (prefixWord ++ tailWord_462746) baseStart_462746 baseEnd_462746 := by
    simpa [prefixWord, tailWord_462746, baseEnd_462746] using wordTrace_append hprefix tailTrace_462746
  have hstable : (prefixWord ++ tailWord_462746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462746).length < 2 ^ (prefixWord ++ tailWord_462746).sum := by decide
  have hdescent : baseEnd_462746 < baseStart_462746 := by decide
  rcases family_descends (prefixWord ++ tailWord_462746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462805 : List Nat := [1, 3, 2, 3, 2, 10]
def baseStart_462805 : Nat := 118140960795 + 462805 * 2 ^ 59
def prefixEnd_462805 : Nat := 4983230072969 + 3 ^ 40 * 462805 * 2
def baseEnd_462805 : Nat := 3911792828052131802619

theorem tailTrace_462805 : CollatzResearch.WordTrace tailWord_462805 prefixEnd_462805 3911792828052131802619 := by
  unfold tailWord_462805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879885088344000646349869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11253256725562667097566579 16879885088344000646349869)
  ·
    refine ⟨6329956908129000242381201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16879885088344000646349869 6329956908129000242381201)
    ·
      refine ⟨4747467681096750181785901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6329956908129000242381201 4747467681096750181785901)
      ·
        refine ⟨1780300380411281318169713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4747467681096750181785901 1780300380411281318169713)
        ·
          refine ⟨1335225285308460988627285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780300380411281318169713 1335225285308460988627285)
          ·
            refine ⟨3911792828052131802619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1335225285308460988627285 3911792828052131802619)
            ·
              rfl

theorem cell21_462805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 10].length) (baseStart_462805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462805 prefixEnd_462805 := by exact prefixLift 462805
  have htrace : WordTrace (prefixWord ++ tailWord_462805) baseStart_462805 baseEnd_462805 := by
    simpa [prefixWord, tailWord_462805, baseEnd_462805] using wordTrace_append hprefix tailTrace_462805
  have hstable : (prefixWord ++ tailWord_462805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462805).length < 2 ^ (prefixWord ++ tailWord_462805).sum := by decide
  have hdescent : baseEnd_462805 < baseStart_462805 := by decide
  rcases family_descends (prefixWord ++ tailWord_462805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462853 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 3]
def baseStart_462853 : Nat := 118140960795 + 462853 * 2 ^ 59
def prefixEnd_462853 : Nat := 4983230072969 + 3 ^ 40 * 462853 * 2
def baseEnd_462853 : Nat := 105629360611370141870615

theorem tailTrace_462853 : CollatzResearch.WordTrace tailWord_462853 prefixEnd_462853 105629360611370141870615 := by
  unfold tailWord_462853
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881635792170104844097213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254423861446736562731475 16881635792170104844097213)
  ·
    refine ⟨6330613422063789316536455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16881635792170104844097213 6330613422063789316536455)
    ·
      refine ⟨9495920133095683974804683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330613422063789316536455 9495920133095683974804683)
      ·
        refine ⟨14243880199643525962207025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495920133095683974804683 14243880199643525962207025)
        ·
          refine ⟨10682910149732644471655269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14243880199643525962207025 10682910149732644471655269)
          ·
            refine ⟨2003045653074870838435363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10682910149732644471655269 2003045653074870838435363)
            ·
              refine ⟨3004568479612306257653045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003045653074870838435363 3004568479612306257653045)
              ·
                refine ⟨281678294963653711654973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3004568479612306257653045 281678294963653711654973)
                ·
                  refine ⟨105629360611370141870615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281678294963653711654973 105629360611370141870615)
                  ·
                    rfl

theorem cell21_462853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_462853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462853 prefixEnd_462853 := by exact prefixLift 462853
  have htrace : WordTrace (prefixWord ++ tailWord_462853) baseStart_462853 baseEnd_462853 := by
    simpa [prefixWord, tailWord_462853, baseEnd_462853] using wordTrace_append hprefix tailTrace_462853
  have hstable : (prefixWord ++ tailWord_462853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462853).length < 2 ^ (prefixWord ++ tailWord_462853).sum := by decide
  have hdescent : baseEnd_462853 < baseStart_462853 := by decide
  rcases family_descends (prefixWord ++ tailWord_462853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462867 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_462867 : Nat := 118140960795 + 462867 * 2 ^ 59
def prefixEnd_462867 : Nat := 4983230072969 + 3 ^ 40 * 462867 * 2
def baseEnd_462867 : Nat := 105632555602109228637253

theorem tailTrace_462867 : CollatzResearch.WordTrace tailWord_462867 prefixEnd_462867 105632555602109228637253 := by
  unfold tailWord_462867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16882146414119385235106855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254764276079590156737903 16882146414119385235106855)
  ·
    refine ⟨25323219621179077852660283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16882146414119385235106855 25323219621179077852660283)
    ·
      refine ⟨37984829431768616778990425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25323219621179077852660283 37984829431768616778990425)
      ·
        refine ⟨28488622073826462584242819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37984829431768616778990425 28488622073826462584242819)
        ·
          refine ⟨42732933110739693876364229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28488622073826462584242819 42732933110739693876364229)
          ·
            refine ⟨8012424958263692601818293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42732933110739693876364229 8012424958263692601818293)
            ·
              refine ⟨751164839837221181420465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8012424958263692601818293 751164839837221181420465)
              ·
                refine ⟨563373629877915886065349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751164839837221181420465 563373629877915886065349)
                ·
                  refine ⟨105632555602109228637253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563373629877915886065349 105632555602109228637253)
                  ·
                    rfl

theorem cell21_462867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_462867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462867 prefixEnd_462867 := by exact prefixLift 462867
  have htrace : WordTrace (prefixWord ++ tailWord_462867) baseStart_462867 baseEnd_462867 := by
    simpa [prefixWord, tailWord_462867, baseEnd_462867] using wordTrace_append hprefix tailTrace_462867
  have hstable : (prefixWord ++ tailWord_462867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462867).length < 2 ^ (prefixWord ++ tailWord_462867).sum := by decide
  have hdescent : baseEnd_462867 < baseStart_462867 := by decide
  rcases family_descends (prefixWord ++ tailWord_462867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462895 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_462895 : Nat := 118140960795 + 462895 * 2 ^ 59
def prefixEnd_462895 : Nat := 4983230072969 + 3 ^ 40 * 462895 * 2
def baseEnd_462895 : Nat := 105638945583587402170529

theorem tailTrace_462895 : CollatzResearch.WordTrace tailWord_462895 prefixEnd_462895 105638945583587402170529 := by
  unfold tailWord_462895
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883167658017946017126139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11255445105345297344750759 16883167658017946017126139)
  ·
    refine ⟨25324751487026919025689209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16883167658017946017126139 25324751487026919025689209)
    ·
      refine ⟨18993563615270189269266907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25324751487026919025689209 18993563615270189269266907)
      ·
        refine ⟨28490345422905283903900361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18993563615270189269266907 28490345422905283903900361)
        ·
          refine ⟨21367759067178962927925271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28490345422905283903900361 21367759067178962927925271)
          ·
            refine ⟨32051638600768444391887907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21367759067178962927925271 32051638600768444391887907)
            ·
              refine ⟨48077457901152666587831861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32051638600768444391887907 48077457901152666587831861)
              ·
                refine ⟨4507261678233062492609237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48077457901152666587831861 4507261678233062492609237)
                ·
                  refine ⟨105638945583587402170529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4507261678233062492609237 105638945583587402170529)
                  ·
                    rfl

theorem cell21_462895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_462895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462895 prefixEnd_462895 := by exact prefixLift 462895
  have htrace : WordTrace (prefixWord ++ tailWord_462895) baseStart_462895 baseEnd_462895 := by
    simpa [prefixWord, tailWord_462895, baseEnd_462895] using wordTrace_append hprefix tailTrace_462895
  have hstable : (prefixWord ++ tailWord_462895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462895).length < 2 ^ (prefixWord ++ tailWord_462895).sum := by decide
  have hdescent : baseEnd_462895 < baseStart_462895 := by decide
  rcases family_descends (prefixWord ++ tailWord_462895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462898 : List Nat := [3, 2, 1, 1, 2, 3, 4, 5]
def baseStart_462898 : Nat := 118140960795 + 462898 * 2 ^ 59
def prefixEnd_462898 : Nat := 4983230072969 + 3 ^ 40 * 462898 * 2
def baseEnd_462898 : Nat := 35213210074820021206841

theorem tailTrace_462898 : CollatzResearch.WordTrace tailWord_462898 prefixEnd_462898 35213210074820021206841 := by
  unfold tailWord_462898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220819269251769382371337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11255518051338051686323565 4220819269251769382371337)
  ·
    refine ⟨3165614451938827036778503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220819269251769382371337 3165614451938827036778503)
    ·
      refine ⟨4748421677908240555167755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165614451938827036778503 4748421677908240555167755)
      ·
        refine ⟨7122632516862360832751633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748421677908240555167755 7122632516862360832751633)
        ·
          refine ⟨5341974387646770624563725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7122632516862360832751633 5341974387646770624563725)
          ·
            refine ⟨2003240395367538984211397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5341974387646770624563725 2003240395367538984211397)
            ·
              refine ⟨375607574131413559539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2003240395367538984211397 375607574131413559539637)
              ·
                refine ⟨35213210074820021206841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375607574131413559539637 35213210074820021206841)
                ·
                  rfl

theorem cell21_462898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_462898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462898 prefixEnd_462898 := by exact prefixLift 462898
  have htrace : WordTrace (prefixWord ++ tailWord_462898) baseStart_462898 baseEnd_462898 := by
    simpa [prefixWord, tailWord_462898, baseEnd_462898] using wordTrace_append hprefix tailTrace_462898
  have hstable : (prefixWord ++ tailWord_462898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462898).length < 2 ^ (prefixWord ++ tailWord_462898).sum := by decide
  have hdescent : baseEnd_462898 < baseStart_462898 := by decide
  rcases family_descends (prefixWord ++ tailWord_462898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462957 : List Nat := [1, 5, 1, 1, 2, 1, 1, 9]
def baseStart_462957 : Nat := 118140960795 + 462957 * 2 ^ 59
def prefixEnd_462957 : Nat := 4983230072969 + 3 ^ 40 * 462957 * 2
def baseEnd_462957 : Nat := 35217698276096357379023

theorem tailTrace_462957 : CollatzResearch.WordTrace tailWord_462957 prefixEnd_462957 35217698276096357379023 := by
  unfold tailWord_462957
  simp only [CollatzResearch.WordTrace]
  refine ⟨16885428983793330605883125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11256952655862220403922083 16885428983793330605883125)
  ·
    refine ⟨1583008967230624744301543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16885428983793330605883125 1583008967230624744301543)
    ·
      refine ⟨2374513450845937116452315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583008967230624744301543 2374513450845937116452315)
      ·
        refine ⟨3561770176268905674678473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374513450845937116452315 3561770176268905674678473)
        ·
          refine ⟨2671327632201679256008855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561770176268905674678473 2671327632201679256008855)
          ·
            refine ⟨4006991448302518884013283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671327632201679256008855 4006991448302518884013283)
            ·
              refine ⟨6010487172453778326019925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006991448302518884013283 6010487172453778326019925)
              ·
                refine ⟨35217698276096357379023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6010487172453778326019925 35217698276096357379023)
                ·
                  rfl

theorem cell21_462957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_462957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462957 prefixEnd_462957 := by exact prefixLift 462957
  have htrace : WordTrace (prefixWord ++ tailWord_462957) baseStart_462957 baseEnd_462957 := by
    simpa [prefixWord, tailWord_462957, baseEnd_462957] using wordTrace_append hprefix tailTrace_462957
  have hstable : (prefixWord ++ tailWord_462957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462957).length < 2 ^ (prefixWord ++ tailWord_462957).sum := by decide
  have hdescent : baseEnd_462957 < baseStart_462957 := by decide
  rcases family_descends (prefixWord ++ tailWord_462957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462974 : List Nat := [4, 2, 4, 11]
def baseStart_462974 : Nat := 118140960795 + 462974 * 2 ^ 59
def prefixEnd_462974 : Nat := 4983230072969 + 3 ^ 40 * 462974 * 2
def baseEnd_462974 : Nat := 434802364032513664007

theorem tailTrace_462974 : CollatzResearch.WordTrace tailWord_462974 prefixEnd_462974 434802364032513664007 := by
  unfold tailWord_462974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110756128091467813656497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11257366016487828339501317 2110756128091467813656497)
  ·
    refine ⟨1583067096068600860242373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2110756128091467813656497 1583067096068600860242373)
    ·
      refine ⟨296825080512862661295445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1583067096068600860242373 296825080512862661295445)
      ·
        refine ⟨434802364032513664007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 296825080512862661295445 434802364032513664007)
        ·
          rfl

theorem cell21_462974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 11].length) (baseStart_462974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_462974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_462974 prefixEnd_462974 := by exact prefixLift 462974
  have htrace : WordTrace (prefixWord ++ tailWord_462974) baseStart_462974 baseEnd_462974 := by
    simpa [prefixWord, tailWord_462974, baseEnd_462974] using wordTrace_append hprefix tailTrace_462974
  have hstable : (prefixWord ++ tailWord_462974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462974).length < 2 ^ (prefixWord ++ tailWord_462974).sum := by decide
  have hdescent : baseEnd_462974 < baseStart_462974 := by decide
  rcases family_descends (prefixWord ++ tailWord_462974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463028 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_463028 : Nat := 118140960795 + 463028 * 2 ^ 59
def prefixEnd_463028 : Nat := 4983230072969 + 3 ^ 40 * 463028 * 2
def baseEnd_463028 : Nat := 105669297995608726453591

theorem tailTrace_463028 : CollatzResearch.WordTrace tailWord_463028 prefixEnd_463028 105669297995608726453591 := by
  unfold tailWord_463028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444009283268054865858869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11258679044357406487811825 8444009283268054865858869)
  ·
    refine ⟨791625870306380143674269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8444009283268054865858869 791625870306380143674269)
    ·
      refine ⟨296859701364892553877851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 791625870306380143674269 296859701364892553877851)
      ·
        refine ⟨445289552047338830816777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296859701364892553877851 445289552047338830816777)
        ·
          refine ⟨333967164035504123112583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445289552047338830816777 333967164035504123112583)
          ·
            refine ⟨500950746053256184668875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333967164035504123112583 500950746053256184668875)
            ·
              refine ⟨751426119079884277003313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500950746053256184668875 751426119079884277003313)
              ·
                refine ⟨563569589309913207752485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751426119079884277003313 563569589309913207752485)
                ·
                  refine ⟨105669297995608726453591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563569589309913207752485 105669297995608726453591)
                  ·
                    rfl

theorem cell21_463028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_463028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463028 prefixEnd_463028 := by exact prefixLift 463028
  have htrace : WordTrace (prefixWord ++ tailWord_463028) baseStart_463028 baseEnd_463028 := by
    simpa [prefixWord, tailWord_463028, baseEnd_463028] using wordTrace_append hprefix tailTrace_463028
  have hstable : (prefixWord ++ tailWord_463028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463028).length < 2 ^ (prefixWord ++ tailWord_463028).sum := by decide
  have hdescent : baseEnd_463028 < baseStart_463028 := by decide
  rcases family_descends (prefixWord ++ tailWord_463028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463064 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_463064 : Nat := 118140960795 + 463064 * 2 ^ 59
def prefixEnd_463064 : Nat := 4983230072969 + 3 ^ 40 * 463064 * 2
def baseEnd_463064 : Nat := 105677513686080663853517

theorem tailTrace_463064 : CollatzResearch.WordTrace tailWord_463064 prefixEnd_463064 105677513686080663853517 := by
  unfold tailWord_463064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444665797202843940014123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11259554396270458586685497 8444665797202843940014123)
  ·
    refine ⟨12666998695804265910021185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8444665797202843940014123 12666998695804265910021185)
    ·
      refine ⟨9500249021853199432515889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12666998695804265910021185 9500249021853199432515889)
      ·
        refine ⟨7125186766389899574386917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9500249021853199432515889 7125186766389899574386917)
        ·
          refine ⟨1335972518698106170197547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7125186766389899574386917 1335972518698106170197547)
          ·
            refine ⟨2003958778047159255296321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335972518698106170197547 2003958778047159255296321)
            ·
              refine ⟨1502969083535369441472241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003958778047159255296321 1502969083535369441472241)
              ·
                refine ⟨1127226812651527081104181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502969083535369441472241 1127226812651527081104181)
                ·
                  refine ⟨105677513686080663853517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127226812651527081104181 105677513686080663853517)
                  ·
                    rfl

theorem cell21_463064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_463064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463064 prefixEnd_463064 := by exact prefixLift 463064
  have htrace : WordTrace (prefixWord ++ tailWord_463064) baseStart_463064 baseEnd_463064 := by
    simpa [prefixWord, tailWord_463064, baseEnd_463064] using wordTrace_append hprefix tailTrace_463064
  have hstable : (prefixWord ++ tailWord_463064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463064).length < 2 ^ (prefixWord ++ tailWord_463064).sum := by decide
  have hdescent : baseEnd_463064 < baseStart_463064 := by decide
  rcases family_descends (prefixWord ++ tailWord_463064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463098 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_463098 : Nat := 118140960795 + 463098 * 2 ^ 59
def prefixEnd_463098 : Nat := 4983230072969 + 3 ^ 40 * 463098 * 2
def baseEnd_463098 : Nat := 105685272949304160286781

theorem tailTrace_463098 : CollatzResearch.WordTrace tailWord_463098 prefixEnd_463098 105685272949304160286781 := by
  unfold tailWord_463098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222642919070627921691487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11260381117521674457843965 4222642919070627921691487)
  ·
    refine ⟨6333964378605941882537231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4222642919070627921691487 6333964378605941882537231)
    ·
      refine ⟨9500946567908912823805847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333964378605941882537231 9500946567908912823805847)
      ·
        refine ⟨14251419851863369235708771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9500946567908912823805847 14251419851863369235708771)
        ·
          refine ⟨21377129777795053853563157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14251419851863369235708771 21377129777795053853563157)
          ·
            refine ⟨1002052958334143149385773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21377129777795053853563157 1002052958334143149385773)
            ·
              refine ⟨375769859375303681019665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002052958334143149385773 375769859375303681019665)
              ·
                refine ⟨281827394531477760764749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375769859375303681019665 281827394531477760764749)
                ·
                  refine ⟨105685272949304160286781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281827394531477760764749 105685272949304160286781)
                  ·
                    rfl

theorem cell21_463098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_463098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463098 prefixEnd_463098 := by exact prefixLift 463098
  have htrace : WordTrace (prefixWord ++ tailWord_463098) baseStart_463098 baseEnd_463098 := by
    simpa [prefixWord, tailWord_463098, baseEnd_463098] using wordTrace_append hprefix tailTrace_463098
  have hstable : (prefixWord ++ tailWord_463098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463098).length < 2 ^ (prefixWord ++ tailWord_463098).sum := by decide
  have hdescent : baseEnd_463098 < baseStart_463098 := by decide
  rcases family_descends (prefixWord ++ tailWord_463098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463112 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_463112 : Nat := 118140960795 + 463112 * 2 ^ 59
def prefixEnd_463112 : Nat := 4983230072969 + 3 ^ 40 * 463112 * 2
def baseEnd_463112 : Nat := 105688467940043247053419

theorem tailTrace_463112 : CollatzResearch.WordTrace tailWord_463112 prefixEnd_463112 105688467940043247053419 := by
  unfold tailWord_463112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445541149115896038887795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11260721532154528051850393 8445541149115896038887795)
  ·
    refine ⟨12668311723673844058331693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8445541149115896038887795 12668311723673844058331693)
    ·
      refine ⟨4750616896377691521874385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12668311723673844058331693 4750616896377691521874385)
      ·
        refine ⟨3562962672283268641405789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750616896377691521874385 3562962672283268641405789)
        ·
          refine ⟨1336111002106225740527171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3562962672283268641405789 1336111002106225740527171)
          ·
            refine ⟨2004166503159338610790757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336111002106225740527171 2004166503159338610790757)
            ·
              refine ⟨375781219342375989523267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2004166503159338610790757 375781219342375989523267)
              ·
                refine ⟨563671829013563984284901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375781219342375989523267 563671829013563984284901)
                ·
                  refine ⟨105688467940043247053419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563671829013563984284901 105688467940043247053419)
                  ·
                    rfl

theorem cell21_463112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_463112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463112 prefixEnd_463112 := by exact prefixLift 463112
  have htrace : WordTrace (prefixWord ++ tailWord_463112) baseStart_463112 baseEnd_463112 := by
    simpa [prefixWord, tailWord_463112, baseEnd_463112] using wordTrace_append hprefix tailTrace_463112
  have hstable : (prefixWord ++ tailWord_463112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463112).length < 2 ^ (prefixWord ++ tailWord_463112).sum := by decide
  have hdescent : baseEnd_463112 < baseStart_463112 := by decide
  rcases family_descends (prefixWord ++ tailWord_463112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463123 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_463123 : Nat := 118140960795 + 463123 * 2 ^ 59
def prefixEnd_463123 : Nat := 4983230072969 + 3 ^ 40 * 463123 * 2
def baseEnd_463123 : Nat := 105690978289909672370063

theorem tailTrace_463123 : CollatzResearch.WordTrace tailWord_463123 prefixEnd_463123 105690978289909672370063 := by
  unfold tailWord_463123
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891483501191940956426023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11260989000794627304284015 16891483501191940956426023)
  ·
    refine ⟨25337225251787911434639035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891483501191940956426023 25337225251787911434639035)
    ·
      refine ⟨38005837877681867151958553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25337225251787911434639035 38005837877681867151958553)
      ·
        refine ⟨28504378408261400363968915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38005837877681867151958553 28504378408261400363968915)
        ·
          refine ⟨42756567612392100545953373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28504378408261400363968915 42756567612392100545953373)
          ·
            refine ⟨16033712854647037704732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42756567612392100545953373 16033712854647037704732515)
            ·
              refine ⟨24050569281970556557098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16033712854647037704732515 24050569281970556557098773)
              ·
                refine ⟨1127370435092369838614005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24050569281970556557098773 1127370435092369838614005)
                ·
                  refine ⟨105690978289909672370063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127370435092369838614005 105690978289909672370063)
                  ·
                    rfl

theorem cell21_463123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_463123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463123 prefixEnd_463123 := by exact prefixLift 463123
  have htrace : WordTrace (prefixWord ++ tailWord_463123) baseStart_463123 baseEnd_463123 := by
    simpa [prefixWord, tailWord_463123, baseEnd_463123] using wordTrace_append hprefix tailTrace_463123
  have hstable : (prefixWord ++ tailWord_463123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463123).length < 2 ^ (prefixWord ++ tailWord_463123).sum := by decide
  have hdescent : baseEnd_463123 < baseStart_463123 := by decide
  rcases family_descends (prefixWord ++ tailWord_463123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463143 : List Nat := [1, 1, 8, 1, 1, 9]
def baseStart_463143 : Nat := 118140960795 + 463143 * 2 ^ 59
def prefixEnd_463143 : Nat := 4983230072969 + 3 ^ 40 * 463143 * 2
def baseEnd_463143 : Nat := 3914649724533114149507

theorem tailTrace_463143 : CollatzResearch.WordTrace tailWord_463143 prefixEnd_463143 3914649724533114149507 := by
  unfold tailWord_463143
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892212961119484372154083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11261475307412989581436055 16892212961119484372154083)
  ·
    refine ⟨25338319441679226558231125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16892212961119484372154083 25338319441679226558231125)
    ·
      refine ⟨296933430957178436229271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 25338319441679226558231125 296933430957178436229271)
      ·
        refine ⟨445400146435767654343907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296933430957178436229271 445400146435767654343907)
        ·
          refine ⟨668100219653651481515861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445400146435767654343907 668100219653651481515861)
          ·
            refine ⟨3914649724533114149507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 668100219653651481515861 3914649724533114149507)
            ·
              rfl

theorem cell21_463143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 9].length) (baseStart_463143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463143 prefixEnd_463143 := by exact prefixLift 463143
  have htrace : WordTrace (prefixWord ++ tailWord_463143) baseStart_463143 baseEnd_463143 := by
    simpa [prefixWord, tailWord_463143, baseEnd_463143] using wordTrace_append hprefix tailTrace_463143
  have hstable : (prefixWord ++ tailWord_463143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463143).length < 2 ^ (prefixWord ++ tailWord_463143).sum := by decide
  have hdescent : baseEnd_463143 < baseStart_463143 := by decide
  rcases family_descends (prefixWord ++ tailWord_463143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463149 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 3]
def baseStart_463149 : Nat := 118140960795 + 463149 * 2 ^ 59
def prefixEnd_463149 : Nat := 4983230072969 + 3 ^ 40 * 463149 * 2
def baseEnd_463149 : Nat := 105696911844139404936677

theorem tailTrace_463149 : CollatzResearch.WordTrace tailWord_463149 prefixEnd_463149 105696911844139404936677 := by
  unfold tailWord_463149
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892431799097747396872501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11261621199398498264581667 16892431799097747396872501)
  ·
    refine ⟨1583665481165413818456797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16892431799097747396872501 1583665481165413818456797)
    ·
      refine ⟨593874555437030181921299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1583665481165413818456797 593874555437030181921299)
      ·
        refine ⟨890811833155545272881949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593874555437030181921299 890811833155545272881949)
        ·
          refine ⟨334054437433329477330731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890811833155545272881949 334054437433329477330731)
          ·
            refine ⟨501081656149994215996097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334054437433329477330731 501081656149994215996097)
            ·
              refine ⟨375811242112495661997073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501081656149994215996097 375811242112495661997073)
              ·
                refine ⟨281858431584371746497805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375811242112495661997073 281858431584371746497805)
                ·
                  refine ⟨105696911844139404936677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281858431584371746497805 105696911844139404936677)
                  ·
                    rfl

theorem cell21_463149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_463149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463149 prefixEnd_463149 := by exact prefixLift 463149
  have htrace : WordTrace (prefixWord ++ tailWord_463149) baseStart_463149 baseEnd_463149 := by
    simpa [prefixWord, tailWord_463149, baseEnd_463149] using wordTrace_append hprefix tailTrace_463149
  have hstable : (prefixWord ++ tailWord_463149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463149).length < 2 ^ (prefixWord ++ tailWord_463149).sum := by decide
  have hdescent : baseEnd_463149 < baseStart_463149 := by decide
  rcases family_descends (prefixWord ++ tailWord_463149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463157 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 3]
def baseStart_463157 : Nat := 118140960795 + 463157 * 2 ^ 59
def prefixEnd_463157 : Nat := 4983230072969 + 3 ^ 40 * 463157 * 2
def baseEnd_463157 : Nat := 105698737553133168803327

theorem tailTrace_463157 : CollatzResearch.WordTrace tailWord_463157 prefixEnd_463157 105698737553133168803327 := by
  unfold tailWord_463157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892723583068764763163725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11261815722045843175442483 16892723583068764763163725)
  ·
    refine ⟨6334771343650786786186397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16892723583068764763163725 6334771343650786786186397)
    ·
      refine ⟨2375539253869045044819899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6334771343650786786186397 2375539253869045044819899)
      ·
        refine ⟨3563308880803567567229849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375539253869045044819899 3563308880803567567229849)
        ·
          refine ⟨2672481660602675675422387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3563308880803567567229849 2672481660602675675422387)
          ·
            refine ⟨4008722490904013513133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672481660602675675422387 4008722490904013513133581)
            ·
              refine ⟨1503270934089005067425093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4008722490904013513133581 1503270934089005067425093)
              ·
                refine ⟨281863300141688450142205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1503270934089005067425093 281863300141688450142205)
                ·
                  refine ⟨105698737553133168803327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281863300141688450142205 105698737553133168803327)
                  ·
                    rfl

theorem cell21_463157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_463157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463157 prefixEnd_463157 := by exact prefixLift 463157
  have htrace : WordTrace (prefixWord ++ tailWord_463157) baseStart_463157 baseEnd_463157 := by
    simpa [prefixWord, tailWord_463157, baseEnd_463157] using wordTrace_append hprefix tailTrace_463157
  have hstable : (prefixWord ++ tailWord_463157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463157).length < 2 ^ (prefixWord ++ tailWord_463157).sum := by decide
  have hdescent : baseEnd_463157 < baseStart_463157 := by decide
  rcases family_descends (prefixWord ++ tailWord_463157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463168 : List Nat := [2, 1, 1, 2, 2, 1, 2, 10]
def baseStart_463168 : Nat := 118140960795 + 463168 * 2 ^ 59
def prefixEnd_463168 : Nat := 4983230072969 + 3 ^ 40 * 463168 * 2
def baseEnd_463168 : Nat := 35233749300999864706657

theorem tailTrace_463168 : CollatzResearch.WordTrace tailWord_463168 prefixEnd_463168 35233749300999864706657 := by
  unfold tailWord_463168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8446562393014456820907079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11262083190685942427876105 8446562393014456820907079)
  ·
    refine ⟨12669843589521685231360619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8446562393014456820907079 12669843589521685231360619)
    ·
      refine ⟨19004765384282527847040929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12669843589521685231360619 19004765384282527847040929)
      ·
        refine ⟨14253574038211895885280697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19004765384282527847040929 14253574038211895885280697)
        ·
          refine ⟨10690180528658921913960523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14253574038211895885280697 10690180528658921913960523)
          ·
            refine ⟨16035270792988382870940785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10690180528658921913960523 16035270792988382870940785)
            ·
              refine ⟨12026453094741287153205589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16035270792988382870940785 12026453094741287153205589)
              ·
                refine ⟨35233749300999864706657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12026453094741287153205589 35233749300999864706657)
                ·
                  rfl

theorem cell21_463168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_463168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463168 prefixEnd_463168 := by exact prefixLift 463168
  have htrace : WordTrace (prefixWord ++ tailWord_463168) baseStart_463168 baseEnd_463168 := by
    simpa [prefixWord, tailWord_463168, baseEnd_463168] using wordTrace_append hprefix tailTrace_463168
  have hstable : (prefixWord ++ tailWord_463168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463168).length < 2 ^ (prefixWord ++ tailWord_463168).sum := by decide
  have hdescent : baseEnd_463168 < baseStart_463168 := by decide
  rcases family_descends (prefixWord ++ tailWord_463168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463216 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_463216 : Nat := 118140960795 + 463216 * 2 ^ 59
def prefixEnd_463216 : Nat := 4983230072969 + 3 ^ 40 * 463216 * 2
def baseEnd_463216 : Nat := 105712202156962177319873

theorem tailTrace_463216 : CollatzResearch.WordTrace tailWord_463216 prefixEnd_463216 105712202156962177319873 := by
  unfold tailWord_463216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447437744927508919780751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11263250326570011893041001 8447437744927508919780751)
  ·
    refine ⟨12671156617391263379671127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8447437744927508919780751 12671156617391263379671127)
    ·
      refine ⟨19006734926086895069506691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671156617391263379671127 19006734926086895069506691)
      ·
        refine ⟨28510102389130342604260037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006734926086895069506691 28510102389130342604260037)
        ·
          refine ⟨5345644197961939238298757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28510102389130342604260037 5345644197961939238298757)
          ·
            refine ⟨1002308287117863607181017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5345644197961939238298757 1002308287117863607181017)
            ·
              refine ⟨751731215338397705385763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002308287117863607181017 751731215338397705385763)
              ·
                refine ⟨1127596823007596558078645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751731215338397705385763 1127596823007596558078645)
                ·
                  refine ⟨105712202156962177319873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127596823007596558078645 105712202156962177319873)
                  ·
                    rfl

theorem cell21_463216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_463216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463216 prefixEnd_463216 := by exact prefixLift 463216
  have htrace : WordTrace (prefixWord ++ tailWord_463216) baseStart_463216 baseEnd_463216 := by
    simpa [prefixWord, tailWord_463216, baseEnd_463216] using wordTrace_append hprefix tailTrace_463216
  have hstable : (prefixWord ++ tailWord_463216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463216).length < 2 ^ (prefixWord ++ tailWord_463216).sum := by decide
  have hdescent : baseEnd_463216 < baseStart_463216 := by decide
  rcases family_descends (prefixWord ++ tailWord_463216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463222 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_463222 : Nat := 118140960795 + 463222 * 2 ^ 59
def prefixEnd_463222 : Nat := 4983230072969 + 3 ^ 40 * 463222 * 2
def baseEnd_463222 : Nat := 105713571438707500219861

theorem tailTrace_463222 : CollatzResearch.WordTrace tailWord_463222 prefixEnd_463222 105713571438707500219861 := by
  unfold tailWord_463222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055943395489580054017495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11263396218555520576186613 1055943395489580054017495)
  ·
    refine ⟨1583915093234370081026243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055943395489580054017495 1583915093234370081026243)
    ·
      refine ⟨2375872639851555121539365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583915093234370081026243 2375872639851555121539365)
      ·
        refine ⟨445476119972166585288631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2375872639851555121539365 445476119972166585288631)
        ·
          refine ⟨668214179958249877932947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445476119972166585288631 668214179958249877932947)
          ·
            refine ⟨1002321269937374816899421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668214179958249877932947 1002321269937374816899421)
            ·
              refine ⟨375870476226515556337283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002321269937374816899421 375870476226515556337283)
              ·
                refine ⟨563805714339773334505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375870476226515556337283 563805714339773334505925)
                ·
                  refine ⟨105713571438707500219861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563805714339773334505925 105713571438707500219861)
                  ·
                    rfl

theorem cell21_463222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_463222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463222 prefixEnd_463222 := by exact prefixLift 463222
  have htrace : WordTrace (prefixWord ++ tailWord_463222) baseStart_463222 baseEnd_463222 := by
    simpa [prefixWord, tailWord_463222, baseEnd_463222] using wordTrace_append hprefix tailTrace_463222
  have hstable : (prefixWord ++ tailWord_463222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463222).length < 2 ^ (prefixWord ++ tailWord_463222).sum := by decide
  have hdescent : baseEnd_463222 < baseStart_463222 := by decide
  rcases family_descends (prefixWord ++ tailWord_463222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463405 : List Nat := [1, 5, 4, 1, 1, 2, 2, 5]
def baseStart_463405 : Nat := 118140960795 + 463405 * 2 ^ 59
def prefixEnd_463405 : Nat := 4983230072969 + 3 ^ 40 * 463405 * 2
def baseEnd_463405 : Nat := 35251778177313282889829

theorem tailTrace_463405 : CollatzResearch.WordTrace tailWord_463405 prefixEnd_463405 35251778177313282889829 := by
  unfold tailWord_463405
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901768886170303118191669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11267845924113535412127779 16901768886170303118191669)
  ·
    refine ⟨1584540833078465917330469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16901768886170303118191669 1584540833078465917330469)
    ·
      refine ⟨297101406202212359499463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1584540833078465917330469 297101406202212359499463)
      ·
        refine ⟨445652109303318539249195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297101406202212359499463 445652109303318539249195)
        ·
          refine ⟨668478163954977808873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445652109303318539249195 668478163954977808873793)
          ·
            refine ⟨501358622966233356655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668478163954977808873793 501358622966233356655345)
            ·
              refine ⟨376018967224675017491509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501358622966233356655345 376018967224675017491509)
              ·
                refine ⟨35251778177313282889829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376018967224675017491509 35251778177313282889829)
                ·
                  rfl

theorem cell21_463405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].length) (baseStart_463405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463405 prefixEnd_463405 := by exact prefixLift 463405
  have htrace : WordTrace (prefixWord ++ tailWord_463405) baseStart_463405 baseEnd_463405 := by
    simpa [prefixWord, tailWord_463405, baseEnd_463405] using wordTrace_append hprefix tailTrace_463405
  have hstable : (prefixWord ++ tailWord_463405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463405).length < 2 ^ (prefixWord ++ tailWord_463405).sum := by decide
  have hdescent : baseEnd_463405 < baseStart_463405 := by decide
  rcases family_descends (prefixWord ++ tailWord_463405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463430 : List Nat := [6, 1, 1, 1, 2, 1, 9]
def baseStart_463430 : Nat := 118140960795 + 463430 * 2 ^ 59
def prefixEnd_463430 : Nat := 4983230072969 + 3 ^ 40 * 463430 * 2
def baseEnd_463430 : Nat := 11751226652505040083641

theorem tailTrace_463430 : CollatzResearch.WordTrace tailWord_463430 prefixEnd_463430 11751226652505040083641 := by
  unfold tailWord_463430
  simp only [CollatzResearch.WordTrace]
  refine ⟨528208772221241637120367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11268453807386488258567829 528208772221241637120367)
  ·
    refine ⟨792313158331862455680551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 528208772221241637120367 792313158331862455680551)
    ·
      refine ⟨1188469737497793683520827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792313158331862455680551 1188469737497793683520827)
      ·
        refine ⟨1782704606246690525281241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188469737497793683520827 1782704606246690525281241)
        ·
          refine ⟨1337028454685017893960931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782704606246690525281241 1337028454685017893960931)
          ·
            refine ⟨2005542682027526840941397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337028454685017893960931 2005542682027526840941397)
            ·
              refine ⟨11751226652505040083641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2005542682027526840941397 11751226652505040083641)
              ·
                rfl

theorem cell21_463430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 9].length) (baseStart_463430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463430 prefixEnd_463430 := by exact prefixLift 463430
  have htrace : WordTrace (prefixWord ++ tailWord_463430) baseStart_463430 baseEnd_463430 := by
    simpa [prefixWord, tailWord_463430, baseEnd_463430] using wordTrace_append hprefix tailTrace_463430
  have hstable : (prefixWord ++ tailWord_463430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463430).length < 2 ^ (prefixWord ++ tailWord_463430).sum := by decide
  have hdescent : baseEnd_463430 < baseStart_463430 := by decide
  rcases family_descends (prefixWord ++ tailWord_463430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463444 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_463444 : Nat := 118140960795 + 463444 * 2 ^ 59
def prefixEnd_463444 : Nat := 4983230072969 + 3 ^ 40 * 463444 * 2
def baseEnd_463444 : Nat := 105764234863284447519407

theorem tailTrace_463444 : CollatzResearch.WordTrace tailWord_463444 prefixEnd_463444 105764234863284447519407 := by
  unfold tailWord_463444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451595666514506389430693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11268794222019341852574257 8451595666514506389430693)
  ·
    refine ⟨1584674187471469948018255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8451595666514506389430693 1584674187471469948018255)
    ·
      refine ⟨2377011281207204922027383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584674187471469948018255 2377011281207204922027383)
      ·
        refine ⟨3565516921810807383041075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377011281207204922027383 3565516921810807383041075)
        ·
          refine ⟨5348275382716211074561613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565516921810807383041075 5348275382716211074561613)
          ·
            refine ⟨2005603268518579152960605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5348275382716211074561613 2005603268518579152960605)
            ·
              refine ⟨752101225694467182360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2005603268518579152960605 752101225694467182360227)
              ·
                refine ⟨1128151838541700773540341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752101225694467182360227 1128151838541700773540341)
                ·
                  refine ⟨105764234863284447519407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128151838541700773540341 105764234863284447519407)
                  ·
                    rfl

theorem cell21_463444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_463444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463444 prefixEnd_463444 := by exact prefixLift 463444
  have htrace : WordTrace (prefixWord ++ tailWord_463444) baseStart_463444 baseEnd_463444 := by
    simpa [prefixWord, tailWord_463444, baseEnd_463444] using wordTrace_append hprefix tailTrace_463444
  have hstable : (prefixWord ++ tailWord_463444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463444).length < 2 ^ (prefixWord ++ tailWord_463444).sum := by decide
  have hdescent : baseEnd_463444 < baseStart_463444 := by decide
  rcases family_descends (prefixWord ++ tailWord_463444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463506 : List Nat := [3, 2, 3, 1, 2, 3, 1, 6]
def baseStart_463506 : Nat := 118140960795 + 463506 * 2 ^ 59
def prefixEnd_463506 : Nat := 4983230072969 + 3 ^ 40 * 463506 * 2
def baseEnd_463506 : Nat := 35259461369328705828649

theorem tailTrace_463506 : CollatzResearch.WordTrace tailWord_463506 prefixEnd_463506 35259461369328705828649 := by
  unfold tailWord_463506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226363164701099341904593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11270301772536264911745581 4226363164701099341904593)
  ·
    refine ⟨3169772373525824506428445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4226363164701099341904593 3169772373525824506428445)
    ·
      refine ⟨1188664640072184189910667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3169772373525824506428445 1188664640072184189910667)
      ·
        refine ⟨1782996960108276284866001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188664640072184189910667 1782996960108276284866001)
        ·
          refine ⟨1337247720081207213649501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782996960108276284866001 1337247720081207213649501)
          ·
            refine ⟨501467895030452705118563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1337247720081207213649501 501467895030452705118563)
            ·
              refine ⟨752201842545679057677845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501467895030452705118563 752201842545679057677845)
              ·
                refine ⟨35259461369328705828649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752201842545679057677845 35259461369328705828649)
                ·
                  rfl

theorem cell21_463506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_463506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463506 prefixEnd_463506 := by exact prefixLift 463506
  have htrace : WordTrace (prefixWord ++ tailWord_463506) baseStart_463506 baseEnd_463506 := by
    simpa [prefixWord, tailWord_463506, baseEnd_463506] using wordTrace_append hprefix tailTrace_463506
  have hstable : (prefixWord ++ tailWord_463506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463506).length < 2 ^ (prefixWord ++ tailWord_463506).sum := by decide
  have hdescent : baseEnd_463506 < baseStart_463506 := by decide
  rcases family_descends (prefixWord ++ tailWord_463506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463520 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_463520 : Nat := 118140960795 + 463520 * 2 ^ 59
def prefixEnd_463520 : Nat := 4983230072969 + 3 ^ 40 * 463520 * 2
def baseEnd_463520 : Nat := 105781579098725204252585

theorem tailTrace_463520 : CollatzResearch.WordTrace tailWord_463520 prefixEnd_463520 105781579098725204252585 := by
  unfold tailWord_463520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452981640376838879314007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11270642187169118505752009 8452981640376838879314007)
  ·
    refine ⟨12679472460565258318971011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8452981640376838879314007 12679472460565258318971011)
    ·
      refine ⟨19019208690847887478456517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12679472460565258318971011 19019208690847887478456517)
      ·
        refine ⟨3566101629533978902210597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19019208690847887478456517 3566101629533978902210597)
        ·
          refine ⟨668644055537621044164487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3566101629533978902210597 668644055537621044164487)
          ·
            refine ⟨1002966083306431566246731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668644055537621044164487 1002966083306431566246731)
            ·
              refine ⟨1504449124959647349370097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002966083306431566246731 1504449124959647349370097)
              ·
                refine ⟨1128336843719735512027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504449124959647349370097 1128336843719735512027573)
                ·
                  refine ⟨105781579098725204252585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128336843719735512027573 105781579098725204252585)
                  ·
                    rfl

theorem cell21_463520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_463520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463520 prefixEnd_463520 := by exact prefixLift 463520
  have htrace : WordTrace (prefixWord ++ tailWord_463520) baseStart_463520 baseEnd_463520 := by
    simpa [prefixWord, tailWord_463520, baseEnd_463520] using wordTrace_append hprefix tailTrace_463520
  have hstable : (prefixWord ++ tailWord_463520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463520).length < 2 ^ (prefixWord ++ tailWord_463520).sum := by decide
  have hdescent : baseEnd_463520 < baseStart_463520 := by decide
  rcases family_descends (prefixWord ++ tailWord_463520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463548 : List Nat := [2, 2, 2, 3, 1, 1, 10]
def baseStart_463548 : Nat := 118140960795 + 463548 * 2 ^ 59
def prefixEnd_463548 : Nat := 4983230072969 + 3 ^ 40 * 463548 * 2
def baseEnd_463548 : Nat := 11754218786689264198429

theorem tailTrace_463548 : CollatzResearch.WordTrace tailWord_463548 prefixEnd_463548 11754218786689264198429 := by
  unfold tailWord_463548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453492262326119270323649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11271323016434825693764865 8453492262326119270323649)
  ·
    refine ⟨6340119196744589452742737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8453492262326119270323649 6340119196744589452742737)
    ·
      refine ⟨4755089397558442089557053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6340119196744589452742737 4755089397558442089557053)
      ·
        refine ⟨1783158524084415783583895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4755089397558442089557053 1783158524084415783583895)
        ·
          refine ⟨2674737786126623675375843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783158524084415783583895 2674737786126623675375843)
          ·
            refine ⟨4012106679189935513063765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674737786126623675375843 4012106679189935513063765)
            ·
              refine ⟨11754218786689264198429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4012106679189935513063765 11754218786689264198429)
              ·
                rfl

theorem cell21_463548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 10].length) (baseStart_463548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463548 prefixEnd_463548 := by exact prefixLift 463548
  have htrace : WordTrace (prefixWord ++ tailWord_463548) baseStart_463548 baseEnd_463548 := by
    simpa [prefixWord, tailWord_463548, baseEnd_463548] using wordTrace_append hprefix tailTrace_463548
  have hstable : (prefixWord ++ tailWord_463548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463548).length < 2 ^ (prefixWord ++ tailWord_463548).sum := by decide
  have hdescent : baseEnd_463548 < baseStart_463548 := by decide
  rcases family_descends (prefixWord ++ tailWord_463548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463551 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_463551 : Nat := 118140960795 + 463551 * 2 ^ 59
def prefixEnd_463551 : Nat := 4983230072969 + 3 ^ 40 * 463551 * 2
def baseEnd_463551 : Nat := 105788653721076039235855

theorem tailTrace_463551 : CollatzResearch.WordTrace tailWord_463551 prefixEnd_463551 105788653721076039235855 := by
  unfold tailWord_463551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907093943641370053006507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11271395962427580035337671 16907093943641370053006507)
  ·
    refine ⟨25360640915462055079509761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16907093943641370053006507 25360640915462055079509761)
    ·
      refine ⟨19020480686596541309632321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25360640915462055079509761 19020480686596541309632321)
      ·
        refine ⟨14265360514947405982224241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19020480686596541309632321 14265360514947405982224241)
        ·
          refine ⟨10699020386210554486668181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265360514947405982224241 10699020386210554486668181)
          ·
            refine ⟨501516580603619741562571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10699020386210554486668181 501516580603619741562571)
            ·
              refine ⟨752274870905429612343857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501516580603619741562571 752274870905429612343857)
              ·
                refine ⟨564206153179072209257893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752274870905429612343857 564206153179072209257893)
                ·
                  refine ⟨105788653721076039235855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564206153179072209257893 105788653721076039235855)
                  ·
                    rfl

theorem cell21_463551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_463551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463551 prefixEnd_463551 := by exact prefixLift 463551
  have htrace : WordTrace (prefixWord ++ tailWord_463551) baseStart_463551 baseEnd_463551 := by
    simpa [prefixWord, tailWord_463551, baseEnd_463551] using wordTrace_append hprefix tailTrace_463551
  have hstable : (prefixWord ++ tailWord_463551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463551).length < 2 ^ (prefixWord ++ tailWord_463551).sum := by decide
  have hdescent : baseEnd_463551 < baseStart_463551 := by decide
  rcases family_descends (prefixWord ++ tailWord_463551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463593 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_463593 : Nat := 118140960795 + 463593 * 2 ^ 59
def prefixEnd_463593 : Nat := 4983230072969 + 3 ^ 40 * 463593 * 2
def baseEnd_463593 : Nat := 105798238693293299535769

theorem tailTrace_463593 : CollatzResearch.WordTrace tailWord_463593 prefixEnd_463593 105798238693293299535769 := by
  unfold tailWord_463593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908625809489211226035433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11272417206326140817356955 16908625809489211226035433)
  ·
    refine ⟨12681469357116908419526575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16908625809489211226035433 12681469357116908419526575)
    ·
      refine ⟨19022204035675362629289863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681469357116908419526575 19022204035675362629289863)
      ·
        refine ⟨28533306053513043943934795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022204035675362629289863 28533306053513043943934795)
        ·
          refine ⟨42799959080269565915902193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28533306053513043943934795 42799959080269565915902193)
          ·
            refine ⟨32099969310202174436926645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42799959080269565915902193 32099969310202174436926645)
            ·
              refine ⟨3009372122831453853461873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32099969310202174436926645 3009372122831453853461873)
              ·
                refine ⟨2257029092123590390096405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009372122831453853461873 2257029092123590390096405)
                ·
                  refine ⟨105798238693293299535769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2257029092123590390096405 105798238693293299535769)
                  ·
                    rfl

theorem cell21_463593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_463593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463593 prefixEnd_463593 := by exact prefixLift 463593
  have htrace : WordTrace (prefixWord ++ tailWord_463593) baseStart_463593 baseEnd_463593 := by
    simpa [prefixWord, tailWord_463593, baseEnd_463593] using wordTrace_append hprefix tailTrace_463593
  have hstable : (prefixWord ++ tailWord_463593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463593).length < 2 ^ (prefixWord ++ tailWord_463593).sum := by decide
  have hdescent : baseEnd_463593 < baseStart_463593 := by decide
  rcases family_descends (prefixWord ++ tailWord_463593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463613 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 3]
def baseStart_463613 : Nat := 118140960795 + 463613 * 2 ^ 59
def prefixEnd_463613 : Nat := 4983230072969 + 3 ^ 40 * 463613 * 2
def baseEnd_463613 : Nat := 105802802965777709202395

theorem tailTrace_463613 : CollatzResearch.WordTrace tailWord_463613 prefixEnd_463613 105802802965777709202395 := by
  unfold tailWord_463613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909355269416754641763493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11272903512944503094508995 16909355269416754641763493)
  ·
    refine ⟨3170504113015641495330655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16909355269416754641763493 3170504113015641495330655)
    ·
      refine ⟨4755756169523462242995983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170504113015641495330655 4755756169523462242995983)
      ·
        refine ⟨7133634254285193364493975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755756169523462242995983 7133634254285193364493975)
        ·
          refine ⟨10700451381427790046740963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133634254285193364493975 10700451381427790046740963)
          ·
            refine ⟨16050677072141685070111445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700451381427790046740963 16050677072141685070111445)
            ·
              refine ⟨376187743878320743830737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16050677072141685070111445 376187743878320743830737)
              ·
                refine ⟨282140807908740557873053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376187743878320743830737 282140807908740557873053)
                ·
                  refine ⟨105802802965777709202395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282140807908740557873053 105802802965777709202395)
                  ·
                    rfl

theorem cell21_463613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_463613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463613 prefixEnd_463613 := by exact prefixLift 463613
  have htrace : WordTrace (prefixWord ++ tailWord_463613) baseStart_463613 baseEnd_463613 := by
    simpa [prefixWord, tailWord_463613, baseEnd_463613] using wordTrace_append hprefix tailTrace_463613
  have hstable : (prefixWord ++ tailWord_463613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463613).length < 2 ^ (prefixWord ++ tailWord_463613).sum := by decide
  have hdescent : baseEnd_463613 < baseStart_463613 := by decide
  rcases family_descends (prefixWord ++ tailWord_463613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463624 : List Nat := [2, 1, 3, 2, 2, 2, 1, 8]
def baseStart_463624 : Nat := 118140960795 + 463624 * 2 ^ 59
def prefixEnd_463624 : Nat := 4983230072969 + 3 ^ 40 * 463624 * 2
def baseEnd_463624 : Nat := 35268437771881378173013

theorem tailTrace_463624 : CollatzResearch.WordTrace tailWord_463624 prefixEnd_463624 35268437771881378173013 := by
  unfold tailWord_463624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454878236188451760206963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11273170981584602346942617 8454878236188451760206963)
  ·
    refine ⟨12682317354282677640310445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8454878236188451760206963 12682317354282677640310445)
    ·
      refine ⟨4755869007856004115116417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12682317354282677640310445 4755869007856004115116417)
      ·
        refine ⟨3566901755892003086337313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4755869007856004115116417 3566901755892003086337313)
        ·
          refine ⟨2675176316919002314752985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566901755892003086337313 2675176316919002314752985)
          ·
            refine ⟨2006382237689251736064739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675176316919002314752985 2006382237689251736064739)
            ·
              refine ⟨3009573356533877604097109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006382237689251736064739 3009573356533877604097109)
              ·
                refine ⟨35268437771881378173013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3009573356533877604097109 35268437771881378173013)
                ·
                  rfl

theorem cell21_463624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_463624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463624 prefixEnd_463624 := by exact prefixLift 463624
  have htrace : WordTrace (prefixWord ++ tailWord_463624) baseStart_463624 baseEnd_463624 := by
    simpa [prefixWord, tailWord_463624, baseEnd_463624] using wordTrace_append hprefix tailTrace_463624
  have hstable : (prefixWord ++ tailWord_463624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463624).length < 2 ^ (prefixWord ++ tailWord_463624).sum := by decide
  have hdescent : baseEnd_463624 < baseStart_463624 := by decide
  rcases family_descends (prefixWord ++ tailWord_463624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463658 : List Nat := [3, 1, 4, 3, 2, 8]
def baseStart_463658 : Nat := 118140960795 + 463658 * 2 ^ 59
def prefixEnd_463658 : Nat := 4983230072969 + 3 ^ 40 * 463658 * 2
def baseEnd_463658 : Nat := 3919002688106208553789

theorem tailTrace_463658 : CollatzResearch.WordTrace tailWord_463658 prefixEnd_463658 3919002688106208553789 := by
  unfold tailWord_463658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227749138563431831787907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11273997702835818218101085 4227749138563431831787907)
  ·
    refine ⟨6341623707845147747681861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4227749138563431831787907 6341623707845147747681861)
    ·
      refine ⟨1189054445220965202690349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6341623707845147747681861 1189054445220965202690349)
      ·
        refine ⟨445895416957861951008881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1189054445220965202690349 445895416957861951008881)
        ·
          refine ⟨334421562718396463256661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445895416957861951008881 334421562718396463256661)
          ·
            refine ⟨3919002688106208553789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 334421562718396463256661 3919002688106208553789)
            ·
              rfl

theorem cell21_463658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 8].length) (baseStart_463658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463658 prefixEnd_463658 := by exact prefixLift 463658
  have htrace : WordTrace (prefixWord ++ tailWord_463658) baseStart_463658 baseEnd_463658 := by
    simpa [prefixWord, tailWord_463658, baseEnd_463658] using wordTrace_append hprefix tailTrace_463658
  have hstable : (prefixWord ++ tailWord_463658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463658).length < 2 ^ (prefixWord ++ tailWord_463658).sum := by decide
  have hdescent : baseEnd_463658 < baseStart_463658 := by decide
  rcases family_descends (prefixWord ++ tailWord_463658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463661 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_463661 : Nat := 118140960795 + 463661 * 2 ^ 59
def prefixEnd_463661 : Nat := 4983230072969 + 3 ^ 40 * 463661 * 2
def baseEnd_463661 : Nat := 105813757219740292402297

theorem tailTrace_463661 : CollatzResearch.WordTrace tailWord_463661 prefixEnd_463661 105813757219740292402297 := by
  unfold tailWord_463661
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911105973242858839510837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274070648828572559673891 16911105973242858839510837)
  ·
    refine ⟨1585416184991518016204141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16911105973242858839510837 1585416184991518016204141)
    ·
      refine ⟨594531069371819256076553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1585416184991518016204141 594531069371819256076553)
      ·
        refine ⟨445898302028864442057415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594531069371819256076553 445898302028864442057415)
        ·
          refine ⟨668847453043296663086123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445898302028864442057415 668847453043296663086123)
          ·
            refine ⟨1003271179564944994629185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668847453043296663086123 1003271179564944994629185)
            ·
              refine ⟨752453384673708745971889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003271179564944994629185 752453384673708745971889)
              ·
                refine ⟨564340038505281559478917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752453384673708745971889 564340038505281559478917)
                ·
                  refine ⟨105813757219740292402297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564340038505281559478917 105813757219740292402297)
                  ·
                    rfl

theorem cell21_463661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_463661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463661 prefixEnd_463661 := by exact prefixLift 463661
  have htrace : WordTrace (prefixWord ++ tailWord_463661) baseStart_463661 baseEnd_463661 := by
    simpa [prefixWord, tailWord_463661, baseEnd_463661] using wordTrace_append hprefix tailTrace_463661
  have hstable : (prefixWord ++ tailWord_463661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463661).length < 2 ^ (prefixWord ++ tailWord_463661).sum := by decide
  have hdescent : baseEnd_463661 < baseStart_463661 := by decide
  rcases family_descends (prefixWord ++ tailWord_463661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463672 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_463672 : Nat := 118140960795 + 463672 * 2 ^ 59
def prefixEnd_463672 : Nat := 4983230072969 + 3 ^ 40 * 463672 * 2
def baseEnd_463672 : Nat := 105816267569606717718941

theorem tailTrace_463672 : CollatzResearch.WordTrace tailWord_463672 prefixEnd_463672 105816267569606717718941 := by
  unfold tailWord_463672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455753588101503859080635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11274338117468671812107513 8455753588101503859080635)
  ·
    refine ⟨12683630382152255788620953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8455753588101503859080635 12683630382152255788620953)
    ·
      refine ⟨9512722786614191841465715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12683630382152255788620953 9512722786614191841465715)
      ·
        refine ⟨14269084179921287762198573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512722786614191841465715 14269084179921287762198573)
        ·
          refine ⟨5350906567470482910824465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14269084179921287762198573 5350906567470482910824465)
          ·
            refine ⟨4013179925602862183118349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350906567470482910824465 4013179925602862183118349)
            ·
              refine ⟨1504942472101073318669381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4013179925602862183118349 1504942472101073318669381)
              ·
                refine ⟨282176713518951247250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1504942472101073318669381 282176713518951247250509)
                ·
                  refine ⟨105816267569606717718941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282176713518951247250509 105816267569606717718941)
                  ·
                    rfl

theorem cell21_463672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_463672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463672 prefixEnd_463672 := by exact prefixLift 463672
  have htrace : WordTrace (prefixWord ++ tailWord_463672) baseStart_463672 baseEnd_463672 := by
    simpa [prefixWord, tailWord_463672, baseEnd_463672] using wordTrace_append hprefix tailTrace_463672
  have hstable : (prefixWord ++ tailWord_463672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463672).length < 2 ^ (prefixWord ++ tailWord_463672).sum := by decide
  have hdescent : baseEnd_463672 < baseStart_463672 := by decide
  rcases family_descends (prefixWord ++ tailWord_463672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463765 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 3]
def baseStart_463765 : Nat := 118140960795 + 463765 * 2 ^ 59
def prefixEnd_463765 : Nat := 4983230072969 + 3 ^ 40 * 463765 * 2
def baseEnd_463765 : Nat := 105837491436659222668751

theorem tailTrace_463765 : CollatzResearch.WordTrace tailWord_463765 prefixEnd_463765 105837491436659222668751 := by
  unfold tailWord_463765
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914899164866084601296749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11276599443244056400864499 16914899164866084601296749)
  ·
    refine ⟨6343087186824781725486281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16914899164866084601296749 6343087186824781725486281)
    ·
      refine ⟨4757315390118586294114711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6343087186824781725486281 4757315390118586294114711)
      ·
        refine ⟨7135973085177879441172067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757315390118586294114711 7135973085177879441172067)
        ·
          refine ⟨10703959627766819161758101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135973085177879441172067 10703959627766819161758101)
          ·
            refine ⟨501748107551569648207411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10703959627766819161758101 501748107551569648207411)
            ·
              refine ⟨752622161327354472311117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501748107551569648207411 752622161327354472311117)
              ·
                refine ⟨282233310497757927116669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752622161327354472311117 282233310497757927116669)
                ·
                  refine ⟨105837491436659222668751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282233310497757927116669 105837491436659222668751)
                  ·
                    rfl

theorem cell21_463765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_463765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463765 prefixEnd_463765 := by exact prefixLift 463765
  have htrace : WordTrace (prefixWord ++ tailWord_463765) baseStart_463765 baseEnd_463765 := by
    simpa [prefixWord, tailWord_463765, baseEnd_463765] using wordTrace_append hprefix tailTrace_463765
  have hstable : (prefixWord ++ tailWord_463765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463765).length < 2 ^ (prefixWord ++ tailWord_463765).sum := by decide
  have hdescent : baseEnd_463765 < baseStart_463765 := by decide
  rcases family_descends (prefixWord ++ tailWord_463765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463793 : List Nat := [1, 2, 2, 4, 3, 1, 2, 6]
def baseStart_463793 : Nat := 118140960795 + 463793 * 2 ^ 59
def prefixEnd_463793 : Nat := 4983230072969 + 3 ^ 40 * 463793 * 2
def baseEnd_463793 : Nat := 35281293806045798734009

theorem tailTrace_463793 : CollatzResearch.WordTrace tailWord_463793 prefixEnd_463793 35281293806045798734009 := by
  unfold tailWord_463793
  simp only [CollatzResearch.WordTrace]
  refine ⟨16915920408764645383316033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11277280272509763588877355 16915920408764645383316033)
  ·
    refine ⟨12686940306573484037487025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16915920408764645383316033 12686940306573484037487025)
    ·
      refine ⟨9515205229930113028115269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12686940306573484037487025 9515205229930113028115269)
      ·
        refine ⟨1784100980611896192771613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9515205229930113028115269 1784100980611896192771613)
        ·
          refine ⟨669037867729461072289355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1784100980611896192771613 669037867729461072289355)
          ·
            refine ⟨1003556801594191608434033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669037867729461072289355 1003556801594191608434033)
            ·
              refine ⟨752667601195643706325525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003556801594191608434033 752667601195643706325525)
              ·
                refine ⟨35281293806045798734009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752667601195643706325525 35281293806045798734009)
                ·
                  rfl

theorem cell21_463793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_463793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463793 prefixEnd_463793 := by exact prefixLift 463793
  have htrace : WordTrace (prefixWord ++ tailWord_463793) baseStart_463793 baseEnd_463793 := by
    simpa [prefixWord, tailWord_463793, baseEnd_463793] using wordTrace_append hprefix tailTrace_463793
  have hstable : (prefixWord ++ tailWord_463793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463793).length < 2 ^ (prefixWord ++ tailWord_463793).sum := by decide
  have hdescent : baseEnd_463793 < baseStart_463793 := by decide
  rcases family_descends (prefixWord ++ tailWord_463793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463796 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_463796 : Nat := 118140960795 + 463796 * 2 ^ 59
def prefixEnd_463796 : Nat := 4983230072969 + 3 ^ 40 * 463796 * 2
def baseEnd_463796 : Nat := 105844566059010057652021

theorem tailTrace_463796 : CollatzResearch.WordTrace tailWord_463796 prefixEnd_463796 105844566059010057652021 := by
  unfold tailWord_463796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458014913876888447837621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11277353218502517930450161 8458014913876888447837621)
  ·
    refine ⟨792938898175958291984777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8458014913876888447837621 792938898175958291984777)
    ·
      refine ⟨594704173631968718988583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 792938898175958291984777 594704173631968718988583)
      ·
        refine ⟨892056260447953078482875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594704173631968718988583 892056260447953078482875)
        ·
          refine ⟨1338084390671929617724313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892056260447953078482875 1338084390671929617724313)
          ·
            refine ⟨1003563293003947213293235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338084390671929617724313 1003563293003947213293235)
            ·
              refine ⟨1505344939505920819939853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003563293003947213293235 1505344939505920819939853)
              ·
                refine ⟨564504352314720307477445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505344939505920819939853 564504352314720307477445)
                ·
                  refine ⟨105844566059010057652021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564504352314720307477445 105844566059010057652021)
                  ·
                    rfl

theorem cell21_463796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_463796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463796 prefixEnd_463796 := by exact prefixLift 463796
  have htrace : WordTrace (prefixWord ++ tailWord_463796) baseStart_463796 baseEnd_463796 := by
    simpa [prefixWord, tailWord_463796, baseEnd_463796] using wordTrace_append hprefix tailTrace_463796
  have hstable : (prefixWord ++ tailWord_463796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463796).length < 2 ^ (prefixWord ++ tailWord_463796).sum := by decide
  have hdescent : baseEnd_463796 < baseStart_463796 := by decide
  rcases family_descends (prefixWord ++ tailWord_463796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463900 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_463900 : Nat := 118140960795 + 463900 * 2 ^ 59
def prefixEnd_463900 : Nat := 4983230072969 + 3 ^ 40 * 463900 * 2
def baseEnd_463900 : Nat := 105868300275928987918475

theorem tailTrace_463900 : CollatzResearch.WordTrace tailWord_463900 prefixEnd_463900 105868300275928987918475 := by
  unfold tailWord_463900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459911509688501328730577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11279882012918001771640769 8459911509688501328730577)
  ·
    refine ⟨6344933632266375996547933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8459911509688501328730577 6344933632266375996547933)
    ·
      refine ⟨2379350112099890998705475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6344933632266375996547933 2379350112099890998705475)
      ·
        refine ⟨3569025168149836498058213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379350112099890998705475 3569025168149836498058213)
        ·
          refine ⟨669192219028094343385915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3569025168149836498058213 669192219028094343385915)
          ·
            refine ⟨1003788328542141515078873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669192219028094343385915 1003788328542141515078873)
            ·
              refine ⟨752841246406606136309155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003788328542141515078873 752841246406606136309155)
              ·
                refine ⟨1129261869609909204463733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752841246406606136309155 1129261869609909204463733)
                ·
                  refine ⟨105868300275928987918475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129261869609909204463733 105868300275928987918475)
                  ·
                    rfl

theorem cell21_463900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_463900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463900 prefixEnd_463900 := by exact prefixLift 463900
  have htrace : WordTrace (prefixWord ++ tailWord_463900) baseStart_463900 baseEnd_463900 := by
    simpa [prefixWord, tailWord_463900, baseEnd_463900] using wordTrace_append hprefix tailTrace_463900
  have hstable : (prefixWord ++ tailWord_463900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463900).length < 2 ^ (prefixWord ++ tailWord_463900).sum := by decide
  have hdescent : baseEnd_463900 < baseStart_463900 := by decide
  rcases family_descends (prefixWord ++ tailWord_463900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463928 : List Nat := [2, 1, 2, 1, 5, 2, 1, 7]
def baseStart_463928 : Nat := 118140960795 + 463928 * 2 ^ 59
def prefixEnd_463928 : Nat := 4983230072969 + 3 ^ 40 * 463928 * 2
def baseEnd_463928 : Nat := 35291563419135720483917

theorem tailTrace_463928 : CollatzResearch.WordTrace tailWord_463928 prefixEnd_463928 35291563419135720483917 := by
  unfold tailWord_463928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460422131637781719740219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11280562842183708959653625 8460422131637781719740219)
  ·
    refine ⟨12690633197456672579610329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8460422131637781719740219 12690633197456672579610329)
    ·
      refine ⟨9517974898092504434707747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12690633197456672579610329 9517974898092504434707747)
      ·
        refine ⟨14276962347138756652061621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517974898092504434707747 14276962347138756652061621)
        ·
          refine ⟨1338465220044258436130777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14276962347138756652061621 1338465220044258436130777)
          ·
            refine ⟨1003848915033193827098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338465220044258436130777 1003848915033193827098083)
            ·
              refine ⟨1505773372549790740647125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003848915033193827098083 1505773372549790740647125)
              ·
                refine ⟨35291563419135720483917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1505773372549790740647125 35291563419135720483917)
                ·
                  rfl

theorem cell21_463928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_463928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463928 prefixEnd_463928 := by exact prefixLift 463928
  have htrace : WordTrace (prefixWord ++ tailWord_463928) baseStart_463928 baseEnd_463928 := by
    simpa [prefixWord, tailWord_463928, baseEnd_463928] using wordTrace_append hprefix tailTrace_463928
  have hstable : (prefixWord ++ tailWord_463928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463928).length < 2 ^ (prefixWord ++ tailWord_463928).sum := by decide
  have hdescent : baseEnd_463928 < baseStart_463928 := by decide
  rcases family_descends (prefixWord ++ tailWord_463928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463934 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_463934 : Nat := 118140960795 + 463934 * 2 ^ 59
def prefixEnd_463934 : Nat := 4983230072969 + 3 ^ 40 * 463934 * 2
def baseEnd_463934 : Nat := 105876059539152484351739

theorem tailTrace_463934 : CollatzResearch.WordTrace tailWord_463934 prefixEnd_463934 105876059539152484351739 := by
  unfold tailWord_463934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115132887656728308024857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11280708734169217642799237 2115132887656728308024857)
  ·
    refine ⟨1586349665742546231018643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2115132887656728308024857 1586349665742546231018643)
    ·
      refine ⟨2379524498613819346527965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586349665742546231018643 2379524498613819346527965)
      ·
        refine ⟨892321686980182254947987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2379524498613819346527965 892321686980182254947987)
        ·
          refine ⟨1338482530470273382421981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892321686980182254947987 1338482530470273382421981)
          ·
            refine ⟨501930948926352518408243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338482530470273382421981 501930948926352518408243)
            ·
              refine ⟨752896423389528777612365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501930948926352518408243 752896423389528777612365)
              ·
                refine ⟨282336158771073291604637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752896423389528777612365 282336158771073291604637)
                ·
                  refine ⟨105876059539152484351739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282336158771073291604637 105876059539152484351739)
                  ·
                    rfl

theorem cell21_463934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_463934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463934 prefixEnd_463934 := by exact prefixLift 463934
  have htrace : WordTrace (prefixWord ++ tailWord_463934) baseStart_463934 baseEnd_463934 := by
    simpa [prefixWord, tailWord_463934, baseEnd_463934] using wordTrace_append hprefix tailTrace_463934
  have hstable : (prefixWord ++ tailWord_463934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463934).length < 2 ^ (prefixWord ++ tailWord_463934).sum := by decide
  have hdescent : baseEnd_463934 < baseStart_463934 := by decide
  rcases family_descends (prefixWord ++ tailWord_463934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463965 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 4]
def baseStart_463965 : Nat := 118140960795 + 463965 * 2 ^ 59
def prefixEnd_463965 : Nat := 4983230072969 + 3 ^ 40 * 463965 * 2
def baseEnd_463965 : Nat := 105883134161503319335009

theorem tailTrace_463965 : CollatzResearch.WordTrace tailWord_463965 prefixEnd_463965 105883134161503319335009 := by
  unfold tailWord_463965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922193764141518758577349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11281462509427679172384899 16922193764141518758577349)
  ·
    refine ⟨3172911330776534767233253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16922193764141518758577349 3172911330776534767233253)
    ·
      refine ⟨594920874520600268856235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3172911330776534767233253 594920874520600268856235)
      ·
        refine ⟨892381311780900403284353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594920874520600268856235 892381311780900403284353)
        ·
          refine ⟨669285983835675302463265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892381311780900403284353 669285983835675302463265)
          ·
            refine ⟨501964487876756476847449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669285983835675302463265 501964487876756476847449)
            ·
              refine ⟨376473365907567357635587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501964487876756476847449 376473365907567357635587)
              ·
                refine ⟨564710048861351036453381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376473365907567357635587 564710048861351036453381)
                ·
                  refine ⟨105883134161503319335009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564710048861351036453381 105883134161503319335009)
                  ·
                    rfl

theorem cell21_463965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_463965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_463965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_463965 prefixEnd_463965 := by exact prefixLift 463965
  have htrace : WordTrace (prefixWord ++ tailWord_463965) baseStart_463965 baseEnd_463965 := by
    simpa [prefixWord, tailWord_463965, baseEnd_463965] using wordTrace_append hprefix tailTrace_463965
  have hstable : (prefixWord ++ tailWord_463965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463965).length < 2 ^ (prefixWord ++ tailWord_463965).sum := by decide
  have hdescent : baseEnd_463965 < baseStart_463965 := by decide
  rcases family_descends (prefixWord ++ tailWord_463965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464097 : List Nat := [1, 2, 3, 1, 3, 4, 2, 5]
def baseStart_464097 : Nat := 118140960795 + 464097 * 2 ^ 59
def prefixEnd_464097 : Nat := 4983230072969 + 3 ^ 40 * 464097 * 2
def baseEnd_464097 : Nat := 35304419453300141044913

theorem tailTrace_464097 : CollatzResearch.WordTrace tailWord_464097 prefixEnd_464097 35304419453300141044913 := by
  unfold tailWord_464097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16927008199663305302382545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11284672133108870201588363 16927008199663305302382545)
  ·
    refine ⟨12695256149747478976786909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16927008199663305302382545 12695256149747478976786909)
    ·
      refine ⟨4760721056155304616295091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12695256149747478976786909 4760721056155304616295091)
      ·
        refine ⟨7141081584232956924442637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760721056155304616295091 7141081584232956924442637)
        ·
          refine ⟨2677905594087358846665989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7141081584232956924442637 2677905594087358846665989)
          ·
            refine ⟨502107298891379783749873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2677905594087358846665989 502107298891379783749873)
            ·
              refine ⟨376580474168534837812405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502107298891379783749873 376580474168534837812405)
              ·
                refine ⟨35304419453300141044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376580474168534837812405 35304419453300141044913)
                ·
                  rfl

theorem cell21_464097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].length) (baseStart_464097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464097 prefixEnd_464097 := by exact prefixLift 464097
  have htrace : WordTrace (prefixWord ++ tailWord_464097) baseStart_464097 baseEnd_464097 := by
    simpa [prefixWord, tailWord_464097, baseEnd_464097] using wordTrace_append hprefix tailTrace_464097
  have hstable : (prefixWord ++ tailWord_464097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464097).length < 2 ^ (prefixWord ++ tailWord_464097).sum := by decide
  have hdescent : baseEnd_464097 < baseStart_464097 := by decide
  rcases family_descends (prefixWord ++ tailWord_464097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464139 : List Nat := [1, 1, 1, 1, 5, 3, 1, 8]
def baseStart_464139 : Nat := 118140960795 + 464139 * 2 ^ 59
def prefixEnd_464139 : Nat := 4983230072969 + 3 ^ 40 * 464139 * 2
def baseEnd_464139 : Nat := 35307614444039227811551

theorem tailTrace_464139 : CollatzResearch.WordTrace tailWord_464139 prefixEnd_464139 35307614444039227811551 := by
  unfold tailWord_464139
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928540065511146475411471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11285693377007430983607647 16928540065511146475411471)
  ·
    refine ⟨25392810098266719713117207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16928540065511146475411471 25392810098266719713117207)
    ·
      refine ⟨38089215147400079569675811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25392810098266719713117207 38089215147400079569675811)
      ·
        refine ⟨57133822721100119354513717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38089215147400079569675811 57133822721100119354513717)
        ·
          refine ⟨5356295880103136189485661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57133822721100119354513717 5356295880103136189485661)
          ·
            refine ⟨2008610955038676071057123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5356295880103136189485661 2008610955038676071057123)
            ·
              refine ⟨3012916432558014106585685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008610955038676071057123 3012916432558014106585685)
              ·
                refine ⟨35307614444039227811551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3012916432558014106585685 35307614444039227811551)
                ·
                  rfl

theorem cell21_464139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_464139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464139 prefixEnd_464139 := by exact prefixLift 464139
  have htrace : WordTrace (prefixWord ++ tailWord_464139) baseStart_464139 baseEnd_464139 := by
    simpa [prefixWord, tailWord_464139, baseEnd_464139] using wordTrace_append hprefix tailTrace_464139
  have hstable : (prefixWord ++ tailWord_464139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464139).length < 2 ^ (prefixWord ++ tailWord_464139).sum := by decide
  have hdescent : baseEnd_464139 < baseStart_464139 := by decide
  rcases family_descends (prefixWord ++ tailWord_464139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464142 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_464142 : Nat := 118140960795 + 464142 * 2 ^ 59
def prefixEnd_464142 : Nat := 4983230072969 + 3 ^ 40 * 464142 * 2
def baseEnd_464142 : Nat := 105923527972990344884647

theorem tailTrace_464142 : CollatzResearch.WordTrace tailWord_464142 prefixEnd_464142 105923527972990344884647 := by
  unfold tailWord_464142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116081185562534748471335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11285766323000185325180453 2116081185562534748471335)
  ·
    refine ⟨3174121778343802122707003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116081185562534748471335 3174121778343802122707003)
    ·
      refine ⟨4761182667515703184060505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174121778343802122707003 4761182667515703184060505)
      ·
        refine ⟨3570887000636777388045379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761182667515703184060505 3570887000636777388045379)
        ·
          refine ⟨5356330500955166082068069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570887000636777388045379 5356330500955166082068069)
          ·
            refine ⟨1004311968929093640387763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5356330500955166082068069 1004311968929093640387763)
            ·
              refine ⟨1506467953393640460581645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004311968929093640387763 1506467953393640460581645)
              ·
                refine ⟨564925482522615172718117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506467953393640460581645 564925482522615172718117)
                ·
                  refine ⟨105923527972990344884647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564925482522615172718117 105923527972990344884647)
                  ·
                    rfl

theorem cell21_464142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_464142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464142 prefixEnd_464142 := by exact prefixLift 464142
  have htrace : WordTrace (prefixWord ++ tailWord_464142) baseStart_464142 baseEnd_464142 := by
    simpa [prefixWord, tailWord_464142, baseEnd_464142] using wordTrace_append hprefix tailTrace_464142
  have hstable : (prefixWord ++ tailWord_464142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464142).length < 2 ^ (prefixWord ++ tailWord_464142).sum := by decide
  have hdescent : baseEnd_464142 < baseStart_464142 := by decide
  rcases family_descends (prefixWord ++ tailWord_464142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464201 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_464201 : Nat := 118140960795 + 464201 * 2 ^ 59
def prefixEnd_464201 : Nat := 4983230072969 + 3 ^ 40 * 464201 * 2
def baseEnd_464201 : Nat := 105936992576819353401193

theorem tailTrace_464201 : CollatzResearch.WordTrace tailWord_464201 prefixEnd_464201 105936992576819353401193 := by
  unfold tailWord_464201
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930801391286531064168457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11287200927524354042778971 16930801391286531064168457)
  ·
    refine ⟨12698101043464898298126343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16930801391286531064168457 12698101043464898298126343)
    ·
      refine ⟨19047151565197347447189515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698101043464898298126343 19047151565197347447189515)
      ·
        refine ⟨28570727347796021170784273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19047151565197347447189515 28570727347796021170784273)
        ·
          refine ⟨21428045510847015878088205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28570727347796021170784273 21428045510847015878088205)
          ·
            refine ⟨8035517066567630954283077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21428045510847015878088205 8035517066567630954283077)
            ·
              refine ⟨1506659449981430803928077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8035517066567630954283077 1506659449981430803928077)
              ·
                refine ⟨564997293743036551473029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506659449981430803928077 564997293743036551473029)
                ·
                  refine ⟨105936992576819353401193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564997293743036551473029 105936992576819353401193)
                  ·
                    rfl

theorem cell21_464201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_464201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464201 prefixEnd_464201 := by exact prefixLift 464201
  have htrace : WordTrace (prefixWord ++ tailWord_464201) baseStart_464201 baseEnd_464201 := by
    simpa [prefixWord, tailWord_464201, baseEnd_464201] using wordTrace_append hprefix tailTrace_464201
  have hstable : (prefixWord ++ tailWord_464201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464201).length < 2 ^ (prefixWord ++ tailWord_464201).sum := by decide
  have hdescent : baseEnd_464201 < baseStart_464201 := by decide
  rcases family_descends (prefixWord ++ tailWord_464201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464232 : List Nat := [2, 1, 4, 2, 3, 1, 8]
def baseStart_464232 : Nat := 118140960795 + 464232 * 2 ^ 59
def prefixEnd_464232 : Nat := 4983230072969 + 3 ^ 40 * 464232 * 2
def baseEnd_464232 : Nat := 11771563022130020931607

theorem tailTrace_464232 : CollatzResearch.WordTrace tailWord_464232 prefixEnd_464232 11771563022130020931607 := by
  unfold tailWord_464232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465966027087111679273475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11287954702782815572364633 8465966027087111679273475)
  ·
    refine ⟨12698949040630667518910213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465966027087111679273475 12698949040630667518910213)
    ·
      refine ⟨2381052945118250159795665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12698949040630667518910213 2381052945118250159795665)
      ·
        refine ⟨1785789708838687619846749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381052945118250159795665 1785789708838687619846749)
        ·
          refine ⟨669671140814507857442531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1785789708838687619846749 669671140814507857442531)
          ·
            refine ⟨1004506711221761786163797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669671140814507857442531 1004506711221761786163797)
            ·
              refine ⟨11771563022130020931607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1004506711221761786163797 11771563022130020931607)
              ·
                rfl

theorem cell21_464232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 8].length) (baseStart_464232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464232 prefixEnd_464232 := by exact prefixLift 464232
  have htrace : WordTrace (prefixWord ++ tailWord_464232) baseStart_464232 baseEnd_464232 := by
    simpa [prefixWord, tailWord_464232, baseEnd_464232] using wordTrace_append hprefix tailTrace_464232
  have hstable : (prefixWord ++ tailWord_464232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464232).length < 2 ^ (prefixWord ++ tailWord_464232).sum := by decide
  have hdescent : baseEnd_464232 < baseStart_464232 := by decide
  rcases family_descends (prefixWord ++ tailWord_464232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464353 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_464353 : Nat := 118140960795 + 464353 * 2 ^ 59
def prefixEnd_464353 : Nat := 4983230072969 + 3 ^ 40 * 464353 * 2
def baseEnd_464353 : Nat := 105971681047700866867549

theorem tailTrace_464353 : CollatzResearch.WordTrace tailWord_464353 prefixEnd_464353 105971681047700866867549 := by
  unfold tailWord_464353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936345286735861023701713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11290896857823907349134475 16936345286735861023701713)
  ·
    refine ⟨12702258965051895767776285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16936345286735861023701713 12702258965051895767776285)
    ·
      refine ⟨4763347111894460912916107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12702258965051895767776285 4763347111894460912916107)
      ·
        refine ⟨7145020667841691369374161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763347111894460912916107 7145020667841691369374161)
        ·
          refine ⟨5358765500881268527030621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7145020667841691369374161 5358765500881268527030621)
          ·
            refine ⟨2009537062830475697636483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5358765500881268527030621 2009537062830475697636483)
            ·
              refine ⟨3014305594245713546454725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009537062830475697636483 3014305594245713546454725)
              ·
                refine ⟨565182298921071289960261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3014305594245713546454725 565182298921071289960261)
                ·
                  refine ⟨105971681047700866867549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565182298921071289960261 105971681047700866867549)
                  ·
                    rfl

theorem cell21_464353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_464353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464353 prefixEnd_464353 := by exact prefixLift 464353
  have htrace : WordTrace (prefixWord ++ tailWord_464353) baseStart_464353 baseEnd_464353 := by
    simpa [prefixWord, tailWord_464353, baseEnd_464353] using wordTrace_append hprefix tailTrace_464353
  have hstable : (prefixWord ++ tailWord_464353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464353).length < 2 ^ (prefixWord ++ tailWord_464353).sum := by decide
  have hdescent : baseEnd_464353 < baseStart_464353 := by decide
  rcases family_descends (prefixWord ++ tailWord_464353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464367 : List Nat := [1, 1, 2, 1, 4, 1, 5, 6]
def baseStart_464367 : Nat := 118140960795 + 464367 * 2 ^ 59
def prefixEnd_464367 : Nat := 4983230072969 + 3 ^ 40 * 464367 * 2
def baseEnd_464367 : Nat := 35324958679479984544729

theorem tailTrace_464367 : CollatzResearch.WordTrace tailWord_464367 prefixEnd_464367 35324958679479984544729 := by
  unfold tailWord_464367
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936855908685141414711355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11291237272456760943140903 16936855908685141414711355)
  ·
    refine ⟨25405283863027712122067033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16936855908685141414711355 25405283863027712122067033)
    ·
      refine ⟨19053962897270784091550275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25405283863027712122067033 19053962897270784091550275)
      ·
        refine ⟨28580944345906176137325413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053962897270784091550275 28580944345906176137325413)
        ·
          refine ⟨5358927064857408025748515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28580944345906176137325413 5358927064857408025748515)
          ·
            refine ⟨8038390597286112038622773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358927064857408025748515 8038390597286112038622773)
            ·
              refine ⟨753599118495573003620885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8038390597286112038622773 753599118495573003620885)
              ·
                refine ⟨35324958679479984544729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 753599118495573003620885 35324958679479984544729)
                ·
                  rfl

theorem cell21_464367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_464367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464367 prefixEnd_464367 := by exact prefixLift 464367
  have htrace : WordTrace (prefixWord ++ tailWord_464367) baseStart_464367 baseEnd_464367 := by
    simpa [prefixWord, tailWord_464367, baseEnd_464367] using wordTrace_append hprefix tailTrace_464367
  have hstable : (prefixWord ++ tailWord_464367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464367).length < 2 ^ (prefixWord ++ tailWord_464367).sum := by decide
  have hdescent : baseEnd_464367 < baseStart_464367 := by decide
  rcases family_descends (prefixWord ++ tailWord_464367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464370 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_464370 : Nat := 118140960795 + 464370 * 2 ^ 59
def prefixEnd_464370 : Nat := 4983230072969 + 3 ^ 40 * 464370 * 2
def baseEnd_464370 : Nat := 105975560679312615084181

theorem tailTrace_464370 : CollatzResearch.WordTrace tailWord_464370 prefixEnd_464370 105975560679312615084181 := by
  unfold tailWord_464370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234241331918568231767641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11291310218449515284713709 4234241331918568231767641)
  ·
    refine ⟨3175680998938926173825731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4234241331918568231767641 3175680998938926173825731)
    ·
      refine ⟨4763521498408389260738597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175680998938926173825731 4763521498408389260738597)
      ·
        refine ⟨893160280951572986388487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4763521498408389260738597 893160280951572986388487)
        ·
          refine ⟨1339740421427359479582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893160280951572986388487 1339740421427359479582731)
          ·
            refine ⟨2009610632141039219374097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339740421427359479582731 2009610632141039219374097)
            ·
              refine ⟨1507207974105779414530573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009610632141039219374097 1507207974105779414530573)
              ·
                refine ⟨565202990289667280448965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507207974105779414530573 565202990289667280448965)
                ·
                  refine ⟨105975560679312615084181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565202990289667280448965 105975560679312615084181)
                  ·
                    rfl

theorem cell21_464370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_464370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464370 prefixEnd_464370 := by exact prefixLift 464370
  have htrace : WordTrace (prefixWord ++ tailWord_464370) baseStart_464370 baseEnd_464370 := by
    simpa [prefixWord, tailWord_464370, baseEnd_464370] using wordTrace_append hprefix tailTrace_464370
  have hstable : (prefixWord ++ tailWord_464370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464370).length < 2 ^ (prefixWord ++ tailWord_464370).sum := by decide
  have hdescent : baseEnd_464370 < baseStart_464370 := by decide
  rcases family_descends (prefixWord ++ tailWord_464370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464404 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_464404 : Nat := 118140960795 + 464404 * 2 ^ 59
def prefixEnd_464404 : Nat := 4983230072969 + 3 ^ 40 * 464404 * 2
def baseEnd_464404 : Nat := 105983319942536111517445

theorem tailTrace_464404 : CollatzResearch.WordTrace tailWord_464404 prefixEnd_464404 105983319942536111517445 := by
  unfold tailWord_464404
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469102704775548366904133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11292136939700731155872177 8469102704775548366904133)
  ·
    refine ⟨1587956757145415318794525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8469102704775548366904133 1587956757145415318794525)
    ·
      refine ⟨595483783929530744547947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1587956757145415318794525 595483783929530744547947)
      ·
        refine ⟨893225675894296116821921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595483783929530744547947 893225675894296116821921)
        ·
          refine ⟨669919256920722087616441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893225675894296116821921 669919256920722087616441)
          ·
            refine ⟨502439442690541565712331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669919256920722087616441 502439442690541565712331)
            ·
              refine ⟨753659164035812348568497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502439442690541565712331 753659164035812348568497)
              ·
                refine ⟨565244373026859261426373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753659164035812348568497 565244373026859261426373)
                ·
                  refine ⟨105983319942536111517445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565244373026859261426373 105983319942536111517445)
                  ·
                    rfl

theorem cell21_464404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_464404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464404 prefixEnd_464404 := by exact prefixLift 464404
  have htrace : WordTrace (prefixWord ++ tailWord_464404) baseStart_464404 baseEnd_464404 := by
    simpa [prefixWord, tailWord_464404, baseEnd_464404] using wordTrace_append hprefix tailTrace_464404
  have hstable : (prefixWord ++ tailWord_464404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464404).length < 2 ^ (prefixWord ++ tailWord_464404).sum := by decide
  have hdescent : baseEnd_464404 < baseStart_464404 := by decide
  rcases family_descends (prefixWord ++ tailWord_464404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464415 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 3]
def baseStart_464415 : Nat := 118140960795 + 464415 * 2 ^ 59
def prefixEnd_464415 : Nat := 4983230072969 + 3 ^ 40 * 464415 * 2
def baseEnd_464415 : Nat := 105985830292402536834089

theorem tailTrace_464415 : CollatzResearch.WordTrace tailWord_464415 prefixEnd_464415 105985830292402536834089 := by
  unfold tailWord_464415
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938606612511245612458699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11292404408340830408305799 16938606612511245612458699)
  ·
    refine ⟨25407909918766868418688049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16938606612511245612458699 25407909918766868418688049)
    ·
      refine ⟨19055932439075151314016037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25407909918766868418688049 19055932439075151314016037)
      ·
        refine ⟨3572987332326590871378007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19055932439075151314016037 3572987332326590871378007)
        ·
          refine ⟨5359480998489886307067011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572987332326590871378007 5359480998489886307067011)
          ·
            refine ⟨8039221497734829460600517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359480998489886307067011 8039221497734829460600517)
            ·
              refine ⟨1507354030825280523862597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8039221497734829460600517 1507354030825280523862597)
              ·
                refine ⟨282628880779740098224237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1507354030825280523862597 282628880779740098224237)
                ·
                  refine ⟨105985830292402536834089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282628880779740098224237 105985830292402536834089)
                  ·
                    rfl

theorem cell21_464415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].length) (baseStart_464415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464415 prefixEnd_464415 := by exact prefixLift 464415
  have htrace : WordTrace (prefixWord ++ tailWord_464415) baseStart_464415 baseEnd_464415 := by
    simpa [prefixWord, tailWord_464415, baseEnd_464415] using wordTrace_append hprefix tailTrace_464415
  have hstable : (prefixWord ++ tailWord_464415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464415).length < 2 ^ (prefixWord ++ tailWord_464415).sum := by decide
  have hdescent : baseEnd_464415 < baseStart_464415 := by decide
  rcases family_descends (prefixWord ++ tailWord_464415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464457 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_464457 : Nat := 118140960795 + 464457 * 2 ^ 59
def prefixEnd_464457 : Nat := 4983230072969 + 3 ^ 40 * 464457 * 2
def baseEnd_464457 : Nat := 105995415264619797134003

theorem tailTrace_464457 : CollatzResearch.WordTrace tailWord_464457 prefixEnd_464457 105995415264619797134003 := by
  unfold tailWord_464457
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940138478359086785487625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11293425652239391190325083 16940138478359086785487625)
  ·
    refine ⟨12705103858769315089115719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16940138478359086785487625 12705103858769315089115719)
    ·
      refine ⟨19057655788153972633673579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705103858769315089115719 19057655788153972633673579)
      ·
        refine ⟨28586483682230958950510369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19057655788153972633673579 28586483682230958950510369)
        ·
          refine ⟨21439862761673219212882777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28586483682230958950510369 21439862761673219212882777)
          ·
            refine ⟨16079897071254914409662083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21439862761673219212882777 16079897071254914409662083)
            ·
              refine ⟨24119845606882371614493125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079897071254914409662083 24119845606882371614493125)
              ·
                refine ⟨4522471051290444677717461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24119845606882371614493125 4522471051290444677717461)
                ·
                  refine ⟨105995415264619797134003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4522471051290444677717461 105995415264619797134003)
                  ·
                    rfl

theorem cell21_464457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_464457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464457 prefixEnd_464457 := by exact prefixLift 464457
  have htrace : WordTrace (prefixWord ++ tailWord_464457) baseStart_464457 baseEnd_464457 := by
    simpa [prefixWord, tailWord_464457, baseEnd_464457] using wordTrace_append hprefix tailTrace_464457
  have hstable : (prefixWord ++ tailWord_464457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464457).length < 2 ^ (prefixWord ++ tailWord_464457).sum := by decide
  have hdescent : baseEnd_464457 < baseStart_464457 := by decide
  rcases family_descends (prefixWord ++ tailWord_464457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464522 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_464522 : Nat := 118140960795 + 464522 * 2 ^ 59
def prefixEnd_464522 : Nat := 4983230072969 + 3 ^ 40 * 464522 * 2
def baseEnd_464522 : Nat := 106010249150194128550537

theorem tailTrace_464522 : CollatzResearch.WordTrace tailWord_464522 prefixEnd_464522 106010249150194128550537 := by
  unfold tailWord_464522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4235627305780900721650955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11295006148749068591069213 4235627305780900721650955)
  ·
    refine ⟨6353440958671351082476433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4235627305780900721650955 6353440958671351082476433)
    ·
      refine ⟨4765080719003513311857325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6353440958671351082476433 4765080719003513311857325)
      ·
        refine ⟨1786905269626317491946497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4765080719003513311857325 1786905269626317491946497)
        ·
          refine ⟨1340178952219738118959873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786905269626317491946497 1340178952219738118959873)
          ·
            refine ⟨1005134214164803589219905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340178952219738118959873 1005134214164803589219905)
            ·
              refine ⟨753850660623602691914929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005134214164803589219905 753850660623602691914929)
              ·
                refine ⟨565387995467702018936197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753850660623602691914929 565387995467702018936197)
                ·
                  refine ⟨106010249150194128550537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565387995467702018936197 106010249150194128550537)
                  ·
                    rfl

theorem cell21_464522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_464522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464522 prefixEnd_464522 := by exact prefixLift 464522
  have htrace : WordTrace (prefixWord ++ tailWord_464522) baseStart_464522 baseEnd_464522 := by
    simpa [prefixWord, tailWord_464522, baseEnd_464522] using wordTrace_append hprefix tailTrace_464522
  have hstable : (prefixWord ++ tailWord_464522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464522).length < 2 ^ (prefixWord ++ tailWord_464522).sum := by decide
  have hdescent : baseEnd_464522 < baseStart_464522 := by decide
  rcases family_descends (prefixWord ++ tailWord_464522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464533 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_464533 : Nat := 118140960795 + 464533 * 2 ^ 59
def prefixEnd_464533 : Nat := 4983230072969 + 3 ^ 40 * 464533 * 2
def baseEnd_464533 : Nat := 106012759500060553867181

theorem tailTrace_464533 : CollatzResearch.WordTrace tailWord_464533 prefixEnd_464533 106012759500060553867181 := by
  unfold tailWord_464533
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942910426083751765254253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11295273617389167843502835 16942910426083751765254253)
  ·
    refine ⟨6353591409781406911970345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16942910426083751765254253 6353591409781406911970345)
    ·
      refine ⟨4765193557336055183977759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6353591409781406911970345 4765193557336055183977759)
      ·
        refine ⟨7147790336004082775966639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765193557336055183977759 7147790336004082775966639)
        ·
          refine ⟨10721685504006124163949959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147790336004082775966639 10721685504006124163949959)
          ·
            refine ⟨16082528256009186245924939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721685504006124163949959 16082528256009186245924939)
            ·
              refine ⟨24123792384013779368887409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082528256009186245924939 24123792384013779368887409)
              ·
                refine ⟨18092844288010334526665557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24123792384013779368887409 18092844288010334526665557)
                ·
                  refine ⟨106012759500060553867181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18092844288010334526665557 106012759500060553867181)
                  ·
                    rfl

theorem cell21_464533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_464533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464533 prefixEnd_464533 := by exact prefixLift 464533
  have htrace : WordTrace (prefixWord ++ tailWord_464533) baseStart_464533 baseEnd_464533 := by
    simpa [prefixWord, tailWord_464533, baseEnd_464533] using wordTrace_append hprefix tailTrace_464533
  have hstable : (prefixWord ++ tailWord_464533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464533).length < 2 ^ (prefixWord ++ tailWord_464533).sum := by decide
  have hdescent : baseEnd_464533 < baseStart_464533 := by decide
  rcases family_descends (prefixWord ++ tailWord_464533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464536 : List Nat := [2, 1, 2, 4, 1, 4, 1, 6]
def baseStart_464536 : Nat := 118140960795 + 464536 * 2 ^ 59
def prefixEnd_464536 : Nat := 4983230072969 + 3 ^ 40 * 464536 * 2
def baseEnd_464536 : Nat := 35337814713644405105725

theorem tailTrace_464536 : CollatzResearch.WordTrace tailWord_464536 prefixEnd_464536 35337814713644405105725 := by
  unfold tailWord_464536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471509922536441638806731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11295346563381922185075641 8471509922536441638806731)
  ·
    refine ⟨12707264883804662458210097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471509922536441638806731 12707264883804662458210097)
    ·
      refine ⟨9530448662853496843657573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12707264883804662458210097 9530448662853496843657573)
      ·
        refine ⟨1786959124285030658185795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9530448662853496843657573 1786959124285030658185795)
        ·
          refine ⟨2680438686427545987278693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786959124285030658185795 2680438686427545987278693)
          ·
            refine ⟨502582253705164872614755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2680438686427545987278693 502582253705164872614755)
            ·
              refine ⟨753873380557747308922133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502582253705164872614755 753873380557747308922133)
              ·
                refine ⟨35337814713644405105725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 753873380557747308922133 35337814713644405105725)
                ·
                  rfl

theorem cell21_464536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_464536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464536 prefixEnd_464536 := by exact prefixLift 464536
  have htrace : WordTrace (prefixWord ++ tailWord_464536) baseStart_464536 baseEnd_464536 := by
    simpa [prefixWord, tailWord_464536, baseEnd_464536] using wordTrace_append hprefix tailTrace_464536
  have hstable : (prefixWord ++ tailWord_464536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464536).length < 2 ^ (prefixWord ++ tailWord_464536).sum := by decide
  have hdescent : baseEnd_464536 < baseStart_464536 := by decide
  rcases family_descends (prefixWord ++ tailWord_464536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464567 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 3]
def baseStart_464567 : Nat := 118140960795 + 464567 * 2 ^ 59
def prefixEnd_464567 : Nat := 4983230072969 + 3 ^ 40 * 464567 * 2
def baseEnd_464567 : Nat := 106020518763284050300445

theorem tailTrace_464567 : CollatzResearch.WordTrace tailWord_464567 prefixEnd_464567 106020518763284050300445 := by
  unfold tailWord_464567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944150507960575571991955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11296100338640383714661303 16944150507960575571991955)
  ·
    refine ⟨25416225761940863357987933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16944150507960575571991955 25416225761940863357987933)
    ·
      refine ⟨9531084660727823759245475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25416225761940863357987933 9531084660727823759245475)
      ·
        refine ⟨14296626991091735638868213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9531084660727823759245475 14296626991091735638868213)
        ·
          refine ⟨1340308780414850216143895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14296626991091735638868213 1340308780414850216143895)
          ·
            refine ⟨2010463170622275324215843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340308780414850216143895 2010463170622275324215843)
            ·
              refine ⟨3015694755933412986323765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010463170622275324215843 3015694755933412986323765)
              ·
                refine ⟨282721383368757467467853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3015694755933412986323765 282721383368757467467853)
                ·
                  refine ⟨106020518763284050300445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282721383368757467467853 106020518763284050300445)
                  ·
                    rfl

theorem cell21_464567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].length) (baseStart_464567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464567 prefixEnd_464567 := by exact prefixLift 464567
  have htrace : WordTrace (prefixWord ++ tailWord_464567) baseStart_464567 baseEnd_464567 := by
    simpa [prefixWord, tailWord_464567, baseEnd_464567] using wordTrace_append hprefix tailTrace_464567
  have hstable : (prefixWord ++ tailWord_464567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464567).length < 2 ^ (prefixWord ++ tailWord_464567).sum := by decide
  have hdescent : baseEnd_464567 < baseStart_464567 := by decide
  rcases family_descends (prefixWord ++ tailWord_464567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464694 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_464694 : Nat := 118140960795 + 464694 * 2 ^ 59
def prefixEnd_464694 : Nat := 4983230072969 + 3 ^ 40 * 464694 * 2
def baseEnd_464694 : Nat := 106049501893560051683519

theorem tailTrace_464694 : CollatzResearch.WordTrace tailWord_464694 prefixEnd_464694 106049501893560051683519 := by
  unfold tailWord_464694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059298911156279766366571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11299188385666984174576757 1059298911156279766366571)
  ·
    refine ⟨1588948366734419649549857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1059298911156279766366571 1588948366734419649549857)
    ·
      refine ⟨1191711275050814737162393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588948366734419649549857 1191711275050814737162393)
      ·
        refine ⟨893783456288111052871795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191711275050814737162393 893783456288111052871795)
        ·
          refine ⟨1340675184432166579307693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893783456288111052871795 1340675184432166579307693)
          ·
            refine ⟨502753194162062467240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1340675184432166579307693 502753194162062467240385)
            ·
              refine ⟨377064895621546850430289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502753194162062467240385 377064895621546850430289)
              ·
                refine ⟨282798671716160137822717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377064895621546850430289 282798671716160137822717)
                ·
                  refine ⟨106049501893560051683519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282798671716160137822717 106049501893560051683519)
                  ·
                    rfl

theorem cell21_464694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_464694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464694 prefixEnd_464694 := by exact prefixLift 464694
  have htrace : WordTrace (prefixWord ++ tailWord_464694) baseStart_464694 baseEnd_464694 := by
    simpa [prefixWord, tailWord_464694, baseEnd_464694] using wordTrace_append hprefix tailTrace_464694
  have hstable : (prefixWord ++ tailWord_464694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464694).length < 2 ^ (prefixWord ++ tailWord_464694).sum := by decide
  have hdescent : baseEnd_464694 < baseStart_464694 := by decide
  rcases family_descends (prefixWord ++ tailWord_464694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464750 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_464750 : Nat := 118140960795 + 464750 * 2 ^ 59
def prefixEnd_464750 : Nat := 4983230072969 + 3 ^ 40 * 464750 * 2
def baseEnd_464750 : Nat := 106062281856516398750071

theorem tailTrace_464750 : CollatzResearch.WordTrace tailWord_464750 prefixEnd_464750 106062281856516398750071 := by
  unfold tailWord_464750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118853133287199728237963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11300550044198398550602469 2118853133287199728237963)
  ·
    refine ⟨3178279699930799592356945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118853133287199728237963 3178279699930799592356945)
    ·
      refine ⟨2383709774948099694267709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3178279699930799592356945 2383709774948099694267709)
      ·
        refine ⟨893891165605537385350391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2383709774948099694267709 893891165605537385350391)
        ·
          refine ⟨1340836748408306078025587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893891165605537385350391 1340836748408306078025587)
          ·
            refine ⟨2011255122612459117038381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340836748408306078025587 2011255122612459117038381)
            ·
              refine ⟨754220670979672168889393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2011255122612459117038381 754220670979672168889393)
              ·
                refine ⟨565665503234754126667045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754220670979672168889393 565665503234754126667045)
                ·
                  refine ⟨106062281856516398750071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565665503234754126667045 106062281856516398750071)
                  ·
                    rfl

theorem cell21_464750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_464750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464750 prefixEnd_464750 := by exact prefixLift 464750
  have htrace : WordTrace (prefixWord ++ tailWord_464750) baseStart_464750 baseEnd_464750 := by
    simpa [prefixWord, tailWord_464750, baseEnd_464750] using wordTrace_append hprefix tailTrace_464750
  have hstable : (prefixWord ++ tailWord_464750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464750).length < 2 ^ (prefixWord ++ tailWord_464750).sum := by decide
  have hdescent : baseEnd_464750 < baseStart_464750 := by decide
  rcases family_descends (prefixWord ++ tailWord_464750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464798 : List Nat := [4, 3, 1, 3, 2, 1, 7]
def baseStart_464798 : Nat := 118140960795 + 464798 * 2 ^ 59
def prefixEnd_464798 : Nat := 4983230072969 + 3 ^ 40 * 464798 * 2
def baseEnd_464798 : Nat := 11785915123386553549997

theorem tailTrace_464798 : CollatzResearch.WordTrace tailWord_464798 prefixEnd_464798 11785915123386553549997 := by
  unfold tailWord_464798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119071971265462752956381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11301717180082468015767365 2119071971265462752956381)
  ·
    refine ⟨794651989224548532358643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2119071971265462752956381 794651989224548532358643)
    ·
      refine ⟨1191977983836822798537965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794651989224548532358643 1191977983836822798537965)
      ·
        refine ⟨446991743938808549451737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1191977983836822798537965 446991743938808549451737)
        ·
          refine ⟨335243807954106412088803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446991743938808549451737 335243807954106412088803)
          ·
            refine ⟨502865711931159618133205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335243807954106412088803 502865711931159618133205)
            ·
              refine ⟨11785915123386553549997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 502865711931159618133205 11785915123386553549997)
              ·
                rfl

theorem cell21_464798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 7].length) (baseStart_464798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464798 prefixEnd_464798 := by exact prefixLift 464798
  have htrace : WordTrace (prefixWord ++ tailWord_464798) baseStart_464798 baseEnd_464798 := by
    simpa [prefixWord, tailWord_464798, baseEnd_464798] using wordTrace_append hprefix tailTrace_464798
  have hstable : (prefixWord ++ tailWord_464798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464798).length < 2 ^ (prefixWord ++ tailWord_464798).sum := by decide
  have hdescent : baseEnd_464798 < baseStart_464798 := by decide
  rcases family_descends (prefixWord ++ tailWord_464798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464860 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_464860 : Nat := 118140960795 + 464860 * 2 ^ 59
def prefixEnd_464860 : Nat := 4983230072969 + 3 ^ 40 * 464860 * 2
def baseEnd_464860 : Nat := 106087385355180651916513

theorem tailTrace_464860 : CollatzResearch.WordTrace tailWord_464860 prefixEnd_464860 106087385355180651916513 := by
  unfold tailWord_464860
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477418547949543306204017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11303224730599391074938689 8477418547949543306204017)
  ·
    refine ⟨6358063910962157479653013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8477418547949543306204017 6358063910962157479653013)
    ·
      refine ⟨298034245826351131858735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6358063910962157479653013 298034245826351131858735)
      ·
        refine ⟨447051368739526697788103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298034245826351131858735 447051368739526697788103)
        ·
          refine ⟨670577053109290046682155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447051368739526697788103 670577053109290046682155)
          ·
            refine ⟨1005865579663935070023233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670577053109290046682155 1005865579663935070023233)
            ·
              refine ⟨754399184747951302517425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005865579663935070023233 754399184747951302517425)
              ·
                refine ⟨565799388560963476888069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754399184747951302517425 565799388560963476888069)
                ·
                  refine ⟨106087385355180651916513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565799388560963476888069 106087385355180651916513)
                  ·
                    rfl

theorem cell21_464860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_464860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464860 prefixEnd_464860 := by exact prefixLift 464860
  have htrace : WordTrace (prefixWord ++ tailWord_464860) baseStart_464860 baseEnd_464860 := by
    simpa [prefixWord, tailWord_464860, baseEnd_464860] using wordTrace_append hprefix tailTrace_464860
  have hstable : (prefixWord ++ tailWord_464860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464860).length < 2 ^ (prefixWord ++ tailWord_464860).sum := by decide
  have hdescent : baseEnd_464860 < baseStart_464860 := by decide
  rcases family_descends (prefixWord ++ tailWord_464860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464919 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 4]
def baseStart_464919 : Nat := 118140960795 + 464919 * 2 ^ 59
def prefixEnd_464919 : Nat := 4983230072969 + 3 ^ 40 * 464919 * 2
def baseEnd_464919 : Nat := 106100849959009660433059

theorem tailTrace_464919 : CollatzResearch.WordTrace tailWord_464919 prefixEnd_464919 106100849959009660433059 := by
  unfold tailWord_464919
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956989002685339688805811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11304659335123559792537207 16956989002685339688805811)
  ·
    refine ⟨25435483504028009533208717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16956989002685339688805811 25435483504028009533208717)
    ·
      refine ⟨9538306314010503574953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25435483504028009533208717 9538306314010503574953269)
      ·
        refine ⟨894216216938484710151869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9538306314010503574953269 894216216938484710151869)
        ·
          refine ⟨335331081351931766306951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894216216938484710151869 335331081351931766306951)
          ·
            refine ⟨502996622027897649460427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335331081351931766306951 502996622027897649460427)
            ·
              refine ⟨754494933041846474190641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502996622027897649460427 754494933041846474190641)
              ·
                refine ⟨565871199781384855642981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754494933041846474190641 565871199781384855642981)
                ·
                  refine ⟨106100849959009660433059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565871199781384855642981 106100849959009660433059)
                  ·
                    rfl

theorem cell21_464919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].length) (baseStart_464919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464919 prefixEnd_464919 := by exact prefixLift 464919
  have htrace : WordTrace (prefixWord ++ tailWord_464919) baseStart_464919 baseEnd_464919 := by
    simpa [prefixWord, tailWord_464919, baseEnd_464919] using wordTrace_append hprefix tailTrace_464919
  have hstable : (prefixWord ++ tailWord_464919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464919).length < 2 ^ (prefixWord ++ tailWord_464919).sum := by decide
  have hdescent : baseEnd_464919 < baseStart_464919 := by decide
  rcases family_descends (prefixWord ++ tailWord_464919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464930 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_464930 : Nat := 118140960795 + 464930 * 2 ^ 59
def prefixEnd_464930 : Nat := 4983230072969 + 3 ^ 40 * 464930 * 2
def baseEnd_464930 : Nat := 106103360308876085749703

theorem tailTrace_464930 : CollatzResearch.WordTrace tailWord_464930 prefixEnd_464930 106103360308876085749703 := by
  unfold tailWord_464930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239347551411372141864061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11304926803763659044970829 4239347551411372141864061)
  ·
    refine ⟨1589755331779264553199023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4239347551411372141864061 1589755331779264553199023)
    ·
      refine ⟨2384632997668896829798535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589755331779264553199023 2384632997668896829798535)
      ·
        refine ⟨3576949496503345244697803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384632997668896829798535 3576949496503345244697803)
        ·
          refine ⟨5365424244755017867046705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576949496503345244697803 5365424244755017867046705)
          ·
            refine ⟨4024068183566263400285029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5365424244755017867046705 4024068183566263400285029)
            ·
              refine ⟨754512784418674387553443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4024068183566263400285029 754512784418674387553443)
              ·
                refine ⟨1131769176628011581330165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754512784418674387553443 1131769176628011581330165)
                ·
                  refine ⟨106103360308876085749703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131769176628011581330165 106103360308876085749703)
                  ·
                    rfl

theorem cell21_464930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_464930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_464930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_464930 prefixEnd_464930 := by exact prefixLift 464930
  have htrace : WordTrace (prefixWord ++ tailWord_464930) baseStart_464930 baseEnd_464930 := by
    simpa [prefixWord, tailWord_464930, baseEnd_464930] using wordTrace_append hprefix tailTrace_464930
  have hstable : (prefixWord ++ tailWord_464930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464930).length < 2 ^ (prefixWord ++ tailWord_464930).sum := by decide
  have hdescent : baseEnd_464930 < baseStart_464930 := by decide
  rcases family_descends (prefixWord ++ tailWord_464930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465034 : List Nat := [3, 1, 2, 3, 1, 11]
def baseStart_465034 : Nat := 118140960795 + 465034 * 2 ^ 59
def prefixEnd_465034 : Nat := 4983230072969 + 3 ^ 40 * 465034 * 2
def baseEnd_465034 : Nat := 3930633130585000593191

theorem tailTrace_465034 : CollatzResearch.WordTrace tailWord_465034 prefixEnd_465034 3930633130585000593191 := by
  unfold tailWord_465034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240295849317178582310539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11307455598179142886161437 4240295849317178582310539)
  ·
    refine ⟨6360443773975767873465809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240295849317178582310539 6360443773975767873465809)
    ·
      refine ⟨4770332830481825905099357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6360443773975767873465809 4770332830481825905099357)
      ·
        refine ⟨1788874811430684714412259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4770332830481825905099357 1788874811430684714412259)
        ·
          refine ⟨2683312217146027071618389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788874811430684714412259 2683312217146027071618389)
          ·
            refine ⟨3930633130585000593191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2683312217146027071618389 3930633130585000593191)
            ·
              rfl

theorem cell21_465034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 11].length) (baseStart_465034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465034 prefixEnd_465034 := by exact prefixLift 465034
  have htrace : WordTrace (prefixWord ++ tailWord_465034) baseStart_465034 baseEnd_465034 := by
    simpa [prefixWord, tailWord_465034, baseEnd_465034] using wordTrace_append hprefix tailTrace_465034
  have hstable : (prefixWord ++ tailWord_465034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465034).length < 2 ^ (prefixWord ++ tailWord_465034).sum := by decide
  have hdescent : baseEnd_465034 < baseStart_465034 := by decide
  rcases family_descends (prefixWord ++ tailWord_465034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465082 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_465082 : Nat := 118140960795 + 465082 * 2 ^ 59
def prefixEnd_465082 : Nat := 4983230072969 + 3 ^ 40 * 465082 * 2
def baseEnd_465082 : Nat := 106138048779757599216059

theorem tailTrace_465082 : CollatzResearch.WordTrace tailWord_465082 prefixEnd_465082 106138048779757599216059 := by
  unfold tailWord_465082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240733525273704631747375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11308622734063212351326333 4240733525273704631747375)
  ·
    refine ⟨6361100287910556947621063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240733525273704631747375 6361100287910556947621063)
    ·
      refine ⟨9541650431865835421431595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361100287910556947621063 9541650431865835421431595)
      ·
        refine ⟨14312475647798753132147393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541650431865835421431595 14312475647798753132147393)
        ·
          refine ⟨10734356735849064849110545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14312475647798753132147393 10734356735849064849110545)
          ·
            refine ⟨8050767551886798636832909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734356735849064849110545 8050767551886798636832909)
            ·
              refine ⟨3019037831957549488812341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050767551886798636832909 3019037831957549488812341)
              ·
                refine ⟨283034796746020264576157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3019037831957549488812341 283034796746020264576157)
                ·
                  refine ⟨106138048779757599216059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283034796746020264576157 106138048779757599216059)
                  ·
                    rfl

theorem cell21_465082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_465082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465082 prefixEnd_465082 := by exact prefixLift 465082
  have htrace : WordTrace (prefixWord ++ tailWord_465082) baseStart_465082 baseEnd_465082 := by
    simpa [prefixWord, tailWord_465082, baseEnd_465082] using wordTrace_append hprefix tailTrace_465082
  have hstable : (prefixWord ++ tailWord_465082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465082).length < 2 ^ (prefixWord ++ tailWord_465082).sum := by decide
  have hdescent : baseEnd_465082 < baseStart_465082 := by decide
  rcases family_descends (prefixWord ++ tailWord_465082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465127 : List Nat := [1, 1, 5, 3, 1, 2, 1, 7]
def baseStart_465127 : Nat := 118140960795 + 465127 * 2 ^ 59
def prefixEnd_465127 : Nat := 4983230072969 + 3 ^ 40 * 465127 * 2
def baseEnd_465127 : Nat := 35382772797615840321989

theorem tailTrace_465127 : CollatzResearch.WordTrace tailWord_465127 prefixEnd_465127 35382772797615840321989 := by
  unfold tailWord_465127
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964575385931791212377635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309716923954527474918423 16964575385931791212377635)
  ·
    refine ⟨25446863078897686818566453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964575385931791212377635 25446863078897686818566453)
    ·
      refine ⟨2385643413646658139240605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25446863078897686818566453 2385643413646658139240605)
      ·
        refine ⟨894616280117496802215227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2385643413646658139240605 894616280117496802215227)
        ·
          refine ⟨1341924420176245203322841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894616280117496802215227 1341924420176245203322841)
          ·
            refine ⟨1006443315132183902492131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341924420176245203322841 1006443315132183902492131)
            ·
              refine ⟨1509664972698275853738197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006443315132183902492131 1509664972698275853738197)
              ·
                refine ⟨35382772797615840321989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1509664972698275853738197 35382772797615840321989)
                ·
                  rfl

theorem cell21_465127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_465127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465127 prefixEnd_465127 := by exact prefixLift 465127
  have htrace : WordTrace (prefixWord ++ tailWord_465127) baseStart_465127 baseEnd_465127 := by
    simpa [prefixWord, tailWord_465127, baseEnd_465127] using wordTrace_append hprefix tailTrace_465127
  have hstable : (prefixWord ++ tailWord_465127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465127).length < 2 ^ (prefixWord ++ tailWord_465127).sum := by decide
  have hdescent : baseEnd_465127 < baseStart_465127 := by decide
  rcases family_descends (prefixWord ++ tailWord_465127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465133 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 3]
def baseStart_465133 : Nat := 118140960795 + 465133 * 2 ^ 59
def prefixEnd_465133 : Nat := 4983230072969 + 3 ^ 40 * 465133 * 2
def baseEnd_465133 : Nat := 106149687674592843865955

theorem tailTrace_465133 : CollatzResearch.WordTrace tailWord_465133 prefixEnd_465133 106149687674592843865955 := by
  unfold tailWord_465133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964794223910054237096053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309862815940036158064035 16964794223910054237096053)
  ·
    refine ⟨1590449458491567584727755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16964794223910054237096053 1590449458491567584727755)
    ·
      refine ⟨2385674187737351377091633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590449458491567584727755 2385674187737351377091633)
      ·
        refine ⟨1789255640803013532818725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385674187737351377091633 1789255640803013532818725)
        ·
          refine ⟨335485432650565037403511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1789255640803013532818725 335485432650565037403511)
          ·
            refine ⟨503228148975847556105267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335485432650565037403511 503228148975847556105267)
            ·
              refine ⟨754842223463771334157901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503228148975847556105267 754842223463771334157901)
              ·
                refine ⟨283065833798914250309213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 754842223463771334157901 283065833798914250309213)
                ·
                  refine ⟨106149687674592843865955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283065833798914250309213 106149687674592843865955)
                  ·
                    rfl

theorem cell21_465133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_465133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465133 prefixEnd_465133 := by exact prefixLift 465133
  have htrace : WordTrace (prefixWord ++ tailWord_465133) baseStart_465133 baseEnd_465133 := by
    simpa [prefixWord, tailWord_465133, baseEnd_465133] using wordTrace_append hprefix tailTrace_465133
  have hstable : (prefixWord ++ tailWord_465133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465133).length < 2 ^ (prefixWord ++ tailWord_465133).sum := by decide
  have hdescent : baseEnd_465133 < baseStart_465133 := by decide
  rcases family_descends (prefixWord ++ tailWord_465133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465155 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_465155 : Nat := 118140960795 + 465155 * 2 ^ 59
def prefixEnd_465155 : Nat := 4983230072969 + 3 ^ 40 * 465155 * 2
def baseEnd_465155 : Nat := 106154708374325694499243

theorem tailTrace_465155 : CollatzResearch.WordTrace tailWord_465155 prefixEnd_465155 106154708374325694499243 := by
  unfold tailWord_465155
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965596629830351994396919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11310397753220234662931279 16965596629830351994396919)
  ·
    refine ⟨25448394944745527991595379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16965596629830351994396919 25448394944745527991595379)
    ·
      refine ⟨38172592417118291987393069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25448394944745527991595379 38172592417118291987393069)
      ·
        refine ⟨14314722156419359495272401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38172592417118291987393069 14314722156419359495272401)
        ·
          refine ⟨10736041617314519621454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14314722156419359495272401 10736041617314519621454301)
          ·
            refine ⟨4026015606492944858045363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10736041617314519621454301 4026015606492944858045363)
            ·
              refine ⟨6039023409739417287068045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026015606492944858045363 6039023409739417287068045)
              ·
                refine ⟨2264633778652281482650517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6039023409739417287068045 2264633778652281482650517)
                ·
                  refine ⟨106154708374325694499243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2264633778652281482650517 106154708374325694499243)
                  ·
                    rfl

theorem cell21_465155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_465155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465155 prefixEnd_465155 := by exact prefixLift 465155
  have htrace : WordTrace (prefixWord ++ tailWord_465155) baseStart_465155 baseEnd_465155 := by
    simpa [prefixWord, tailWord_465155, baseEnd_465155] using wordTrace_append hprefix tailTrace_465155
  have hstable : (prefixWord ++ tailWord_465155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465155).length < 2 ^ (prefixWord ++ tailWord_465155).sum := by decide
  have hdescent : baseEnd_465155 < baseStart_465155 := by decide
  rcases family_descends (prefixWord ++ tailWord_465155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465200 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_465200 : Nat := 118140960795 + 465200 * 2 ^ 59
def prefixEnd_465200 : Nat := 4983230072969 + 3 ^ 40 * 465200 * 2
def baseEnd_465200 : Nat := 106164977987415616249151

theorem tailTrace_465200 : CollatzResearch.WordTrace tailWord_465200 prefixEnd_465200 106164977987415616249151 := by
  unfold tailWord_465200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483618957333662339892527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11311491943111549786523369 8483618957333662339892527)
  ·
    refine ⟨12725428436000493509838791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8483618957333662339892527 12725428436000493509838791)
    ·
      refine ⟨19088142654000740264758187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725428436000493509838791 19088142654000740264758187)
      ·
        refine ⟨28632213981001110397137281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19088142654000740264758187 28632213981001110397137281)
        ·
          refine ⟨21474160485750832797852961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28632213981001110397137281 21474160485750832797852961)
          ·
            refine ⟨16105620364313124598389721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21474160485750832797852961 16105620364313124598389721)
            ·
              refine ⟨12079215273234843448792291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16105620364313124598389721 12079215273234843448792291)
              ·
                refine ⟨18118822909852265173188437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12079215273234843448792291 18118822909852265173188437)
                ·
                  refine ⟨106164977987415616249151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18118822909852265173188437 106164977987415616249151)
                  ·
                    rfl

theorem cell21_465200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_465200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465200 prefixEnd_465200 := by exact prefixLift 465200
  have htrace : WordTrace (prefixWord ++ tailWord_465200) baseStart_465200 baseEnd_465200 := by
    simpa [prefixWord, tailWord_465200, baseEnd_465200] using wordTrace_append hprefix tailTrace_465200
  have hstable : (prefixWord ++ tailWord_465200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465200).length < 2 ^ (prefixWord ++ tailWord_465200).sum := by decide
  have hdescent : baseEnd_465200 < baseStart_465200 := by decide
  rcases family_descends (prefixWord ++ tailWord_465200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465341 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 4]
def baseStart_465341 : Nat := 118140960795 + 465341 * 2 ^ 59
def prefixEnd_465341 : Nat := 4983230072969 + 3 ^ 40 * 465341 * 2
def baseEnd_465341 : Nat := 106197156108430704398863

theorem tailTrace_465341 : CollatzResearch.WordTrace tailWord_465341 prefixEnd_465341 106197156108430704398863 := by
  unfold tailWord_465341
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972380607156505760667877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314920404771003840445251 16972380607156505760667877)
  ·
    refine ⟨3182321363841844830125227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16972380607156505760667877 3182321363841844830125227)
    ·
      refine ⟨4773482045762767245187841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182321363841844830125227 4773482045762767245187841)
      ·
        refine ⟨3580111534322075433890881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4773482045762767245187841 3580111534322075433890881)
        ·
          refine ⟨2685083650741556575418161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580111534322075433890881 2685083650741556575418161)
          ·
            refine ⟨2013812738056167431563621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685083650741556575418161 2013812738056167431563621)
            ·
              refine ⟨377589888385531393418179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2013812738056167431563621 377589888385531393418179)
              ·
                refine ⟨566384832578297090127269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377589888385531393418179 566384832578297090127269)
                ·
                  refine ⟨106197156108430704398863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566384832578297090127269 106197156108430704398863)
                  ·
                    rfl

theorem cell21_465341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_465341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465341 prefixEnd_465341 := by exact prefixLift 465341
  have htrace : WordTrace (prefixWord ++ tailWord_465341) baseStart_465341 baseEnd_465341 := by
    simpa [prefixWord, tailWord_465341, baseEnd_465341] using wordTrace_append hprefix tailTrace_465341
  have hstable : (prefixWord ++ tailWord_465341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465341).length < 2 ^ (prefixWord ++ tailWord_465341).sum := by decide
  have hdescent : baseEnd_465341 < baseStart_465341 := by decide
  rcases family_descends (prefixWord ++ tailWord_465341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465378 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_465378 : Nat := 118140960795 + 465378 * 2 ^ 59
def prefixEnd_465378 : Nat := 4983230072969 + 3 ^ 40 * 465378 * 2
def baseEnd_465378 : Nat := 106205600012526862282121

theorem tailTrace_465378 : CollatzResearch.WordTrace tailWord_465378 prefixEnd_465378 106205600012526862282121 := by
  unfold tailWord_465378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243432527005615269941197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11315820072014974053176525 4243432527005615269941197)
  ·
    refine ⟨1591287197627105726227949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4243432527005615269941197 1591287197627105726227949)
    ·
      refine ⟨596732699110164647335481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1591287197627105726227949 596732699110164647335481)
      ·
        refine ⟨447549524332623485501611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596732699110164647335481 447549524332623485501611)
        ·
          refine ⟨671324286498935228252417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447549524332623485501611 671324286498935228252417)
          ·
            refine ⟨503493214874201421189313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671324286498935228252417 503493214874201421189313)
            ·
              refine ⟨377619911155651065891985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503493214874201421189313 377619911155651065891985)
              ·
                refine ⟨283214933366738299418989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377619911155651065891985 283214933366738299418989)
                ·
                  refine ⟨106205600012526862282121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283214933366738299418989 106205600012526862282121)
                  ·
                    rfl

theorem cell21_465378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_465378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465378 prefixEnd_465378 := by exact prefixLift 465378
  have htrace : WordTrace (prefixWord ++ tailWord_465378) baseStart_465378 baseEnd_465378 := by
    simpa [prefixWord, tailWord_465378, baseEnd_465378] using wordTrace_append hprefix tailTrace_465378
  have hstable : (prefixWord ++ tailWord_465378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465378).length < 2 ^ (prefixWord ++ tailWord_465378).sum := by decide
  have hdescent : baseEnd_465378 < baseStart_465378 := by decide
  rcases family_descends (prefixWord ++ tailWord_465378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465431 : List Nat := [1, 1, 3, 6, 1, 1, 8]
def baseStart_465431 : Nat := 118140960795 + 465431 * 2 ^ 59
def prefixEnd_465431 : Nat := 4983230072969 + 3 ^ 40 * 465431 * 2
def baseEnd_465431 : Nat := 11801966148290060877631

theorem tailTrace_465431 : CollatzResearch.WordTrace tailWord_465431 prefixEnd_465431 11801966148290060877631 := by
  unfold tailWord_465431
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975663176830451131444147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11317108784553634087629431 16975663176830451131444147)
  ·
    refine ⟨25463494765245676697166221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16975663176830451131444147 25463494765245676697166221)
    ·
      refine ⟨9548810536967128761437333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25463494765245676697166221 9548810536967128761437333)
      ·
        refine ⟨447600493920334160692375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9548810536967128761437333 447600493920334160692375)
        ·
          refine ⟨671400740880501241038563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447600493920334160692375 671400740880501241038563)
          ·
            refine ⟨1007101111320751861557845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671400740880501241038563 1007101111320751861557845)
            ·
              refine ⟨11801966148290060877631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1007101111320751861557845 11801966148290060877631)
              ·
                rfl

theorem cell21_465431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 8].length) (baseStart_465431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465431 prefixEnd_465431 := by exact prefixLift 465431
  have htrace : WordTrace (prefixWord ++ tailWord_465431) baseStart_465431 baseEnd_465431 := by
    simpa [prefixWord, tailWord_465431, baseEnd_465431] using wordTrace_append hprefix tailTrace_465431
  have hstable : (prefixWord ++ tailWord_465431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465431).length < 2 ^ (prefixWord ++ tailWord_465431).sum := by decide
  have hdescent : baseEnd_465431 < baseStart_465431 := by decide
  rcases family_descends (prefixWord ++ tailWord_465431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465462 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_465462 : Nat := 118140960795 + 465462 * 2 ^ 59
def prefixEnd_465462 : Nat := 4983230072969 + 3 ^ 40 * 465462 * 2
def baseEnd_465462 : Nat := 106224769956961382881949

theorem tailTrace_465462 : CollatzResearch.WordTrace tailWord_465462 prefixEnd_465462 106224769956961382881949 := by
  unfold tailWord_465462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061049614982383964113915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11317862559812095617215093 1061049614982383964113915)
  ·
    refine ⟨1591574422473575946170873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061049614982383964113915 1591574422473575946170873)
    ·
      refine ⟨1193680816855181959628155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591574422473575946170873 1193680816855181959628155)
      ·
        refine ⟨1790521225282772939442233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193680816855181959628155 1790521225282772939442233)
        ·
          refine ⟨1342890918962079704581675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790521225282772939442233 1342890918962079704581675)
          ·
            refine ⟨2014336378443119556872513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342890918962079704581675 2014336378443119556872513)
            ·
              refine ⟨1510752283832339667654385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014336378443119556872513 1510752283832339667654385)
              ·
                refine ⟨1133064212874254750740789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510752283832339667654385 1133064212874254750740789)
                ·
                  refine ⟨106224769956961382881949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1133064212874254750740789 106224769956961382881949)
                  ·
                    rfl

theorem cell21_465462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_465462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465462 prefixEnd_465462 := by exact prefixLift 465462
  have htrace : WordTrace (prefixWord ++ tailWord_465462) baseStart_465462 baseEnd_465462 := by
    simpa [prefixWord, tailWord_465462, baseEnd_465462] using wordTrace_append hprefix tailTrace_465462
  have hstable : (prefixWord ++ tailWord_465462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465462).length < 2 ^ (prefixWord ++ tailWord_465462).sum := by decide
  have hdescent : baseEnd_465462 < baseStart_465462 := by decide
  rcases family_descends (prefixWord ++ tailWord_465462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465479 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 3]
def baseStart_465479 : Nat := 118140960795 + 465479 * 2 ^ 59
def prefixEnd_465479 : Nat := 4983230072969 + 3 ^ 40 * 465479 * 2
def baseEnd_465479 : Nat := 106228649588573131098581

theorem tailTrace_465479 : CollatzResearch.WordTrace tailWord_465479 prefixEnd_465479 106228649588573131098581 := by
  unfold tailWord_465479
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977413880656555329191491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11318275920437703552794327 16977413880656555329191491)
  ·
    refine ⟨25466120820984832993787237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16977413880656555329191491 25466120820984832993787237)
    ·
      refine ⟨4774897653934656186335107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25466120820984832993787237 4774897653934656186335107)
      ·
        refine ⟨7162346480901984279502661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774897653934656186335107 7162346480901984279502661)
        ·
          refine ⟨1342939965169122052406749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7162346480901984279502661 1342939965169122052406749)
          ·
            refine ⟨503602486938420769652531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1342939965169122052406749 503602486938420769652531)
            ·
              refine ⟨755403730407631154478797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503602486938420769652531 755403730407631154478797)
              ·
                refine ⟨283276398902861682929549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755403730407631154478797 283276398902861682929549)
                ·
                  refine ⟨106228649588573131098581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283276398902861682929549 106228649588573131098581)
                  ·
                    rfl

theorem cell21_465479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].length) (baseStart_465479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465479 prefixEnd_465479 := by exact prefixLift 465479
  have htrace : WordTrace (prefixWord ++ tailWord_465479) baseStart_465479 baseEnd_465479 := by
    simpa [prefixWord, tailWord_465479, baseEnd_465479] using wordTrace_append hprefix tailTrace_465479
  have hstable : (prefixWord ++ tailWord_465479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465479).length < 2 ^ (prefixWord ++ tailWord_465479).sum := by decide
  have hdescent : baseEnd_465479 < baseStart_465479 := by decide
  rcases family_descends (prefixWord ++ tailWord_465479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465614 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_465614 : Nat := 118140960795 + 465614 * 2 ^ 59
def prefixEnd_465614 : Nat := 4983230072969 + 3 ^ 40 * 465614 * 2
def baseEnd_465614 : Nat := 106259458427842896348305

theorem tailTrace_465614 : CollatzResearch.WordTrace tailWord_465614 prefixEnd_465614 106259458427842896348305 := by
  unfold tailWord_465614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122792216895934173169487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11321558490111648923570597 2122792216895934173169487)
  ·
    refine ⟨3184188325343901259754231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122792216895934173169487 3184188325343901259754231)
    ·
      refine ⟨4776282488015851889631347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184188325343901259754231 4776282488015851889631347)
      ·
        refine ⟨7164423732023777834447021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776282488015851889631347 7164423732023777834447021)
        ·
          refine ⟨2686658899508916687917633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7164423732023777834447021 2686658899508916687917633)
          ·
            refine ⟨2014994174631687515938225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686658899508916687917633 2014994174631687515938225)
            ·
              refine ⟨1511245630973765636953669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014994174631687515938225 1511245630973765636953669)
              ·
                refine ⟨283358555807581056928813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1511245630973765636953669 283358555807581056928813)
                ·
                  refine ⟨106259458427842896348305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283358555807581056928813 106259458427842896348305)
                  ·
                    rfl

theorem cell21_465614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_465614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465614 prefixEnd_465614 := by exact prefixLift 465614
  have htrace : WordTrace (prefixWord ++ tailWord_465614) baseStart_465614 baseEnd_465614 := by
    simpa [prefixWord, tailWord_465614, baseEnd_465614] using wordTrace_append hprefix tailTrace_465614
  have hstable : (prefixWord ++ tailWord_465614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465614).length < 2 ^ (prefixWord ++ tailWord_465614).sum := by decide
  have hdescent : baseEnd_465614 < baseStart_465614 := by decide
  rcases family_descends (prefixWord ++ tailWord_465614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465625 : List Nat := [1, 2, 1, 2, 3, 2, 2, 8]
def baseStart_465625 : Nat := 118140960795 + 465625 * 2 ^ 59
def prefixEnd_465625 : Nat := 4983230072969 + 3 ^ 40 * 465625 * 2
def baseEnd_465625 : Nat := 35420656259236440554983

theorem tailTrace_465625 : CollatzResearch.WordTrace tailWord_465625 prefixEnd_465625 35420656259236440554983 := by
  unfold tailWord_465625
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982738938127622264006329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11321825958751748176004219 16982738938127622264006329)
  ·
    refine ⟨12737054203595716698004747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16982738938127622264006329 12737054203595716698004747)
    ·
      refine ⟨19105581305393575047007121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737054203595716698004747 19105581305393575047007121)
      ·
        refine ⟨14329185979045181285255341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19105581305393575047007121 14329185979045181285255341)
        ·
          refine ⟨5373444742141942981970753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14329185979045181285255341 5373444742141942981970753)
          ·
            refine ⟨4030083556606457236478065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373444742141942981970753 4030083556606457236478065)
            ·
              refine ⟨3022562667454842927358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030083556606457236478065 3022562667454842927358549)
              ·
                refine ⟨35420656259236440554983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3022562667454842927358549 35420656259236440554983)
                ·
                  rfl

theorem cell21_465625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_465625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465625 prefixEnd_465625 := by exact prefixLift 465625
  have htrace : WordTrace (prefixWord ++ tailWord_465625) baseStart_465625 baseEnd_465625 := by
    simpa [prefixWord, tailWord_465625, baseEnd_465625] using wordTrace_append hprefix tailTrace_465625
  have hstable : (prefixWord ++ tailWord_465625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465625).length < 2 ^ (prefixWord ++ tailWord_465625).sum := by decide
  have hdescent : baseEnd_465625 < baseStart_465625 := by decide
  rcases family_descends (prefixWord ++ tailWord_465625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465673 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 3]
def baseStart_465673 : Nat := 118140960795 + 465673 * 2 ^ 59
def prefixEnd_465673 : Nat := 4983230072969 + 3 ^ 40 * 465673 * 2
def baseEnd_465673 : Nat := 106272923031671904864851

theorem tailTrace_465673 : CollatzResearch.WordTrace tailWord_465673 prefixEnd_465673 106272923031671904864851 := by
  unfold tailWord_465673
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984489641953726461753673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11322993094635817641169115 16984489641953726461753673)
  ·
    refine ⟨12738367231465294846315255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16984489641953726461753673 12738367231465294846315255)
    ·
      refine ⟨19107550847197942269472883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738367231465294846315255 19107550847197942269472883)
      ·
        refine ⟨28661326270796913404209325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107550847197942269472883 28661326270796913404209325)
        ·
          refine ⟨10747997351548842526578497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28661326270796913404209325 10747997351548842526578497)
          ·
            refine ⟨8060998013661631894933873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10747997351548842526578497 8060998013661631894933873)
            ·
              refine ⟨6045748510246223921200405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060998013661631894933873 6045748510246223921200405)
              ·
                refine ⟨283394461417791746306269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6045748510246223921200405 283394461417791746306269)
                ·
                  refine ⟨106272923031671904864851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283394461417791746306269 106272923031671904864851)
                  ·
                    rfl

theorem cell21_465673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_465673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465673 prefixEnd_465673 := by exact prefixLift 465673
  have htrace : WordTrace (prefixWord ++ tailWord_465673) baseStart_465673 baseEnd_465673 := by
    simpa [prefixWord, tailWord_465673, baseEnd_465673] using wordTrace_append hprefix tailTrace_465673
  have hstable : (prefixWord ++ tailWord_465673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465673).length < 2 ^ (prefixWord ++ tailWord_465673).sum := by decide
  have hdescent : baseEnd_465673 < baseStart_465673 := by decide
  rcases family_descends (prefixWord ++ tailWord_465673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465701 : List Nat := [1, 3, 1, 2, 3, 1, 1, 9]
def baseStart_465701 : Nat := 118140960795 + 465701 * 2 ^ 59
def prefixEnd_465701 : Nat := 4983230072969 + 3 ^ 40 * 465701 * 2
def baseEnd_465701 : Nat := 35426437671050026132709

theorem tailTrace_465701 : CollatzResearch.WordTrace tailWord_465701 prefixEnd_465701 35426437671050026132709 := by
  unfold tailWord_465701
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985510885852287243772957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11323673923901524829181971 16985510885852287243772957)
  ·
    refine ⟨6369566582194607716414859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16985510885852287243772957 6369566582194607716414859)
    ·
      refine ⟨9554349873291911574622289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6369566582194607716414859 9554349873291911574622289)
      ·
        refine ⟨7165762404968933680966717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9554349873291911574622289 7165762404968933680966717)
        ·
          refine ⟨2687160901863350130362519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7165762404968933680966717 2687160901863350130362519)
          ·
            refine ⟨4030741352795025195543779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687160901863350130362519 4030741352795025195543779)
            ·
              refine ⟨6046112029192537793315669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030741352795025195543779 6046112029192537793315669)
              ·
                refine ⟨35426437671050026132709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6046112029192537793315669 35426437671050026132709)
                ·
                  rfl

theorem cell21_465701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_465701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465701 prefixEnd_465701 := by exact prefixLift 465701
  have htrace : WordTrace (prefixWord ++ tailWord_465701) baseStart_465701 baseEnd_465701 := by
    simpa [prefixWord, tailWord_465701, baseEnd_465701] using wordTrace_append hprefix tailTrace_465701
  have hstable : (prefixWord ++ tailWord_465701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465701).length < 2 ^ (prefixWord ++ tailWord_465701).sum := by decide
  have hdescent : baseEnd_465701 < baseStart_465701 := by decide
  rcases family_descends (prefixWord ++ tailWord_465701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465718 : List Nat := [5, 1, 2, 2, 11]
def baseStart_465718 : Nat := 118140960795 + 465718 * 2 ^ 59
def prefixEnd_465718 : Nat := 4983230072969 + 3 ^ 40 * 465718 * 2
def baseEnd_465718 : Nat := 1312138180799528723639

theorem tailTrace_465718 : CollatzResearch.WordTrace tailWord_465718 prefixEnd_465718 1312138180799528723639 := by
  unfold tailWord_465718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061633182924418696696363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11324087284527132764761205 1061633182924418696696363)
  ·
    refine ⟨1592449774386628045044545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061633182924418696696363 1592449774386628045044545)
    ·
      refine ⟨1194337330789971033783409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1592449774386628045044545 1194337330789971033783409)
      ·
        refine ⟨895752998092478275337557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194337330789971033783409 895752998092478275337557)
        ·
          refine ⟨1312138180799528723639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 895752998092478275337557 1312138180799528723639)
          ·
            rfl

theorem cell21_465718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 11].length) (baseStart_465718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465718 prefixEnd_465718 := by exact prefixLift 465718
  have htrace : WordTrace (prefixWord ++ tailWord_465718) baseStart_465718 baseEnd_465718 := by
    simpa [prefixWord, tailWord_465718, baseEnd_465718] using wordTrace_append hprefix tailTrace_465718
  have hstable : (prefixWord ++ tailWord_465718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465718).length < 2 ^ (prefixWord ++ tailWord_465718).sum := by decide
  have hdescent : baseEnd_465718 < baseStart_465718 := by decide
  rcases family_descends (prefixWord ++ tailWord_465718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465777 : List Nat := [1, 2, 2, 2, 1, 5, 8]
def baseStart_465777 : Nat := 118140960795 + 465777 * 2 ^ 59
def prefixEnd_465777 : Nat := 4983230072969 + 3 ^ 40 * 465777 * 2
def baseEnd_465777 : Nat := 11810739694287870570145

theorem tailTrace_465777 : CollatzResearch.WordTrace tailWord_465777 prefixEnd_465777 11810739694287870570145 := by
  unfold tailWord_465777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988282833576952223539585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11325521889051301482359723 16988282833576952223539585)
  ·
    refine ⟨12741212125182714167654689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16988282833576952223539585 12741212125182714167654689)
    ·
      refine ⟨9555909093887035625741017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12741212125182714167654689 9555909093887035625741017)
      ·
        refine ⟨7166931820415276719305763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9555909093887035625741017 7166931820415276719305763)
        ·
          refine ⟨10750397730622915078958645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166931820415276719305763 10750397730622915078958645)
          ·
            refine ⟨1007849787245898288652373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10750397730622915078958645 1007849787245898288652373)
            ·
              refine ⟨11810739694287870570145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1007849787245898288652373 11810739694287870570145)
              ·
                rfl

theorem cell21_465777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 8].length) (baseStart_465777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465777 prefixEnd_465777 := by exact prefixLift 465777
  have htrace : WordTrace (prefixWord ++ tailWord_465777) baseStart_465777 baseEnd_465777 := by
    simpa [prefixWord, tailWord_465777, baseEnd_465777] using wordTrace_append hprefix tailTrace_465777
  have hstable : (prefixWord ++ tailWord_465777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465777).length < 2 ^ (prefixWord ++ tailWord_465777).sum := by decide
  have hdescent : baseEnd_465777 < baseStart_465777 := by decide
  rcases family_descends (prefixWord ++ tailWord_465777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465856 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_465856 : Nat := 118140960795 + 465856 * 2 ^ 59
def prefixEnd_465856 : Nat := 4983230072969 + 3 ^ 40 * 465856 * 2
def baseEnd_465856 : Nat := 106314686124904253314477

theorem tailTrace_465856 : CollatzResearch.WordTrace tailWord_465856 prefixEnd_465856 106314686124904253314477 := by
  unfold tailWord_465856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495582100145374357832711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11327442800193832477110281 8495582100145374357832711)
  ·
    refine ⟨12743373150218061536749067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8495582100145374357832711 12743373150218061536749067)
    ·
      refine ⟨19115059725327092305123601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12743373150218061536749067 19115059725327092305123601)
      ·
        refine ⟨14336294793995319228842701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19115059725327092305123601 14336294793995319228842701)
        ·
          refine ⟨5376110547748244710816013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14336294793995319228842701 5376110547748244710816013)
          ·
            refine ⟨2016041455405591766556005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5376110547748244710816013 2016041455405591766556005)
            ·
              refine ⟨378007772888548456229251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2016041455405591766556005 378007772888548456229251)
              ·
                refine ⟨567011659332822684343877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378007772888548456229251 567011659332822684343877)
                ·
                  refine ⟨106314686124904253314477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567011659332822684343877 106314686124904253314477)
                  ·
                    rfl

theorem cell21_465856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_465856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465856 prefixEnd_465856 := by exact prefixLift 465856
  have htrace : WordTrace (prefixWord ++ tailWord_465856) baseStart_465856 baseEnd_465856 := by
    simpa [prefixWord, tailWord_465856, baseEnd_465856] using wordTrace_append hprefix tailTrace_465856
  have hstable : (prefixWord ++ tailWord_465856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465856).length < 2 ^ (prefixWord ++ tailWord_465856).sum := by decide
  have hdescent : baseEnd_465856 < baseStart_465856 := by decide
  rcases family_descends (prefixWord ++ tailWord_465856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465893 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 3]
def baseStart_465893 : Nat := 118140960795 + 465893 * 2 ^ 59
def prefixEnd_465893 : Nat := 4983230072969 + 3 ^ 40 * 465893 * 2
def baseEnd_465893 : Nat := 106323130029000411197735

theorem tailTrace_465893 : CollatzResearch.WordTrace tailWord_465893 prefixEnd_465893 106323130029000411197735 := by
  unfold tailWord_465893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992513701156704034762333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11328342467437802689841555 16992513701156704034762333)
  ·
    refine ⟨6372192637933764013035875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16992513701156704034762333 6372192637933764013035875)
    ·
      refine ⟨9558288956900646019553813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372192637933764013035875 9558288956900646019553813)
      ·
        refine ⟨448044794854717782166585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9558288956900646019553813 448044794854717782166585)
        ·
          refine ⟨336033596141038336624939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448044794854717782166585 336033596141038336624939)
          ·
            refine ⟨504050394211557504937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336033596141038336624939 504050394211557504937409)
            ·
              refine ⟨378037795658668128703057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504050394211557504937409 378037795658668128703057)
              ·
                refine ⟨283528346744001096527293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378037795658668128703057 283528346744001096527293)
                ·
                  refine ⟨106323130029000411197735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283528346744001096527293 106323130029000411197735)
                  ·
                    rfl

theorem cell21_465893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_465893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465893 prefixEnd_465893 := by exact prefixLift 465893
  have htrace : WordTrace (prefixWord ++ tailWord_465893) baseStart_465893 baseEnd_465893 := by
    simpa [prefixWord, tailWord_465893, baseEnd_465893] using wordTrace_append hprefix tailTrace_465893
  have hstable : (prefixWord ++ tailWord_465893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465893).length < 2 ^ (prefixWord ++ tailWord_465893).sum := by decide
  have hdescent : baseEnd_465893 < baseStart_465893 := by decide
  rcases family_descends (prefixWord ++ tailWord_465893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465918 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_465918 : Nat := 118140960795 + 465918 * 2 ^ 59
def prefixEnd_465918 : Nat := 4983230072969 + 3 ^ 40 * 465918 * 2
def baseEnd_465918 : Nat := 106328835369605923281017

theorem tailTrace_465918 : CollatzResearch.WordTrace tailWord_465918 prefixEnd_465918 106328835369605923281017 := by
  unfold tailWord_465918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124178190758266663052801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11328950350710755536281605 2124178190758266663052801)
  ·
    refine ⟨1593133643068699997289601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2124178190758266663052801 1593133643068699997289601)
    ·
      refine ⟨1194850232301524997967201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1593133643068699997289601 1194850232301524997967201)
      ·
        refine ⟨896137674226143748475401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194850232301524997967201 896137674226143748475401)
        ·
          refine ⟨672103255669607811356551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896137674226143748475401 672103255669607811356551)
          ·
            refine ⟨1008154883504411717034827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672103255669607811356551 1008154883504411717034827)
            ·
              refine ⟨1512232325256617575552241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008154883504411717034827 1512232325256617575552241)
              ·
                refine ⟨1134174243942463181664181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512232325256617575552241 1134174243942463181664181)
                ·
                  refine ⟨106328835369605923281017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134174243942463181664181 106328835369605923281017)
                  ·
                    rfl

theorem cell21_465918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_465918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465918 prefixEnd_465918 := by exact prefixLift 465918
  have htrace : WordTrace (prefixWord ++ tailWord_465918) baseStart_465918 baseEnd_465918 := by
    simpa [prefixWord, tailWord_465918, baseEnd_465918] using wordTrace_append hprefix tailTrace_465918
  have hstable : (prefixWord ++ tailWord_465918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465918).length < 2 ^ (prefixWord ++ tailWord_465918).sum := by decide
  have hdescent : baseEnd_465918 < baseStart_465918 := by decide
  rcases family_descends (prefixWord ++ tailWord_465918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465949 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_465949 : Nat := 118140960795 + 465949 * 2 ^ 59
def prefixEnd_465949 : Nat := 4983230072969 + 3 ^ 40 * 465949 * 2
def baseEnd_465949 : Nat := 106335909991956758264287

theorem tailTrace_465949 : CollatzResearch.WordTrace tailWord_465949 prefixEnd_465949 106335909991956758264287 := by
  unfold tailWord_465949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994556188953825598800901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329704125969217065867267 16994556188953825598800901)
  ·
    refine ⟨3186479285428842299775169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16994556188953825598800901 3186479285428842299775169)
    ·
      refine ⟨2389859464071631724831377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3186479285428842299775169 2389859464071631724831377)
      ·
        refine ⟨1792394598053723793623533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2389859464071631724831377 1792394598053723793623533)
        ·
          refine ⟨672147974270146422608825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1792394598053723793623533 672147974270146422608825)
          ·
            refine ⟨504110980702609816956619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672147974270146422608825 504110980702609816956619)
            ·
              refine ⟨756166471053914725434929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504110980702609816956619 756166471053914725434929)
              ·
                refine ⟨567124853290436044076197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756166471053914725434929 567124853290436044076197)
                ·
                  refine ⟨106335909991956758264287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567124853290436044076197 106335909991956758264287)
                  ·
                    rfl

theorem cell21_465949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_465949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_465949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_465949 prefixEnd_465949 := by exact prefixLift 465949
  have htrace : WordTrace (prefixWord ++ tailWord_465949) baseStart_465949 baseEnd_465949 := by
    simpa [prefixWord, tailWord_465949, baseEnd_465949] using wordTrace_append hprefix tailTrace_465949
  have hstable : (prefixWord ++ tailWord_465949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465949).length < 2 ^ (prefixWord ++ tailWord_465949).sum := by decide
  have hdescent : baseEnd_465949 < baseStart_465949 := by decide
  rcases family_descends (prefixWord ++ tailWord_465949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466095 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_466095 : Nat := 118140960795 + 466095 * 2 ^ 59
def prefixEnd_466095 : Nat := 4983230072969 + 3 ^ 40 * 466095 * 2
def baseEnd_466095 : Nat := 106369229181092948830655

theorem tailTrace_466095 : CollatzResearch.WordTrace tailWord_466095 prefixEnd_466095 106369229181092948830655 := by
  unfold tailWord_466095
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999881246424892533615739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11333254164283261689077159 16999881246424892533615739)
  ·
    refine ⟨25499821869637338800423609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16999881246424892533615739 25499821869637338800423609)
    ·
      refine ⟨19124866402228004100317707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25499821869637338800423609 19124866402228004100317707)
      ·
        refine ⟨28687299603342006150476561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19124866402228004100317707 28687299603342006150476561)
        ·
          refine ⟨21515474702506504612857421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28687299603342006150476561 21515474702506504612857421)
          ·
            refine ⟨8068303013439939229821533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21515474702506504612857421 8068303013439939229821533)
            ·
              refine ⟨3025613630039977211183075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8068303013439939229821533 3025613630039977211183075)
              ·
                refine ⟨4538420445059965816774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025613630039977211183075 4538420445059965816774613)
                ·
                  refine ⟨106369229181092948830655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4538420445059965816774613 106369229181092948830655)
                  ·
                    rfl

theorem cell21_466095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_466095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466095 prefixEnd_466095 := by exact prefixLift 466095
  have htrace : WordTrace (prefixWord ++ tailWord_466095) baseStart_466095 baseEnd_466095 := by
    simpa [prefixWord, tailWord_466095, baseEnd_466095] using wordTrace_append hprefix tailTrace_466095
  have hstable : (prefixWord ++ tailWord_466095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466095).length < 2 ^ (prefixWord ++ tailWord_466095).sum := by decide
  have hdescent : baseEnd_466095 < baseStart_466095 := by decide
  rcases family_descends (prefixWord ++ tailWord_466095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466098 : List Nat := [3, 2, 1, 1, 1, 5, 3, 5]
def baseStart_466098 : Nat := 118140960795 + 466098 * 2 ^ 59
def prefixEnd_466098 : Nat := 4983230072969 + 3 ^ 40 * 466098 * 2
def baseEnd_466098 : Nat := 35456637940655203426883

theorem tailTrace_466098 : CollatzResearch.WordTrace tailWord_466098 prefixEnd_466098 35456637940655203426883 := by
  unfold tailWord_466098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4249997666353506011493737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11333327110276016030649965 4249997666353506011493737)
  ·
    refine ⟨3187498249765129508620303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4249997666353506011493737 3187498249765129508620303)
    ·
      refine ⟨4781247374647694262930455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187498249765129508620303 4781247374647694262930455)
      ·
        refine ⟨7171871061971541394395683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781247374647694262930455 7171871061971541394395683)
        ·
          refine ⟨10757806592957312091593525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171871061971541394395683 10757806592957312091593525)
          ·
            refine ⟨1008544368089748008586893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10757806592957312091593525 1008544368089748008586893)
            ·
              refine ⟨378204138033655503220085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1008544368089748008586893 378204138033655503220085)
              ·
                refine ⟨35456637940655203426883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378204138033655503220085 35456637940655203426883)
                ·
                  rfl

theorem cell21_466098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_466098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466098 prefixEnd_466098 := by exact prefixLift 466098
  have htrace : WordTrace (prefixWord ++ tailWord_466098) baseStart_466098 baseEnd_466098 := by
    simpa [prefixWord, tailWord_466098, baseEnd_466098] using wordTrace_append hprefix tailTrace_466098
  have hstable : (prefixWord ++ tailWord_466098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466098).length < 2 ^ (prefixWord ++ tailWord_466098).sum := by decide
  have hdescent : baseEnd_466098 < baseStart_466098 := by decide
  rcases family_descends (prefixWord ++ tailWord_466098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466118 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_466118 : Nat := 118140960795 + 466118 * 2 ^ 59
def prefixEnd_466118 : Nat := 4983230072969 + 3 ^ 40 * 466118 * 2
def baseEnd_466118 : Nat := 106374478094450019947275

theorem tailTrace_466118 : CollatzResearch.WordTrace tailWord_466118 prefixEnd_466118 106374478094450019947275 := by
  unfold tailWord_466118
  simp only [CollatzResearch.WordTrace]
  refine ⟨531272503916923983178219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11333813416894378307802005 531272503916923983178219)
  ·
    refine ⟨796908755875385974767329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531272503916923983178219 796908755875385974767329)
    ·
      refine ⟨597681566906539481075497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796908755875385974767329 597681566906539481075497)
      ·
        refine ⟨448261175179904610806623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597681566906539481075497 448261175179904610806623)
        ·
          refine ⟨672391762769856916209935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448261175179904610806623 672391762769856916209935)
          ·
            refine ⟨1008587644154785374314903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672391762769856916209935 1008587644154785374314903)
            ·
              refine ⟨1512881466232178061472355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008587644154785374314903 1512881466232178061472355)
              ·
                refine ⟨2269322199348267092208533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512881466232178061472355 2269322199348267092208533)
                ·
                  refine ⟨106374478094450019947275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2269322199348267092208533 106374478094450019947275)
                  ·
                    rfl

theorem cell21_466118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_466118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466118 prefixEnd_466118 := by exact prefixLift 466118
  have htrace : WordTrace (prefixWord ++ tailWord_466118) baseStart_466118 baseEnd_466118 := by
    simpa [prefixWord, tailWord_466118, baseEnd_466118] using wordTrace_append hprefix tailTrace_466118
  have hstable : (prefixWord ++ tailWord_466118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466118).length < 2 ^ (prefixWord ++ tailWord_466118).sum := by decide
  have hdescent : baseEnd_466118 < baseStart_466118 := by decide
  rcases family_descends (prefixWord ++ tailWord_466118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466174 : List Nat := [4, 2, 2, 1, 1, 4, 7]
def baseStart_466174 : Nat := 118140960795 + 466174 * 2 ^ 59
def prefixEnd_466174 : Nat := 4983230072969 + 3 ^ 40 * 466174 * 2
def baseEnd_466174 : Nat := 11820806450822929668203

theorem tailTrace_466174 : CollatzResearch.WordTrace tailWord_466174 prefixEnd_466174 11820806450822929668203 := by
  unfold tailWord_466174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125345326642336128217697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11335175075425792683827717 2125345326642336128217697)
  ·
    refine ⟨1594008994981752096163273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2125345326642336128217697 1594008994981752096163273)
    ·
      refine ⟨1195506746236314072122455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594008994981752096163273 1195506746236314072122455)
      ·
        refine ⟨1793260119354471108183683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195506746236314072122455 1793260119354471108183683)
        ·
          refine ⟨2689890179031706662275525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793260119354471108183683 2689890179031706662275525)
          ·
            refine ⟨504354408568444999176661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2689890179031706662275525 504354408568444999176661)
            ·
              refine ⟨11820806450822929668203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 504354408568444999176661 11820806450822929668203)
              ·
                rfl

theorem cell21_466174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 7].length) (baseStart_466174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466174 prefixEnd_466174 := by exact prefixLift 466174
  have htrace : WordTrace (prefixWord ++ tailWord_466174) baseStart_466174 baseEnd_466174 := by
    simpa [prefixWord, tailWord_466174, baseEnd_466174] using wordTrace_append hprefix tailTrace_466174
  have hstable : (prefixWord ++ tailWord_466174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466174).length < 2 ^ (prefixWord ++ tailWord_466174).sum := by decide
  have hdescent : baseEnd_466174 < baseStart_466174 := by decide
  rcases family_descends (prefixWord ++ tailWord_466174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466188 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_466188 : Nat := 118140960795 + 466188 * 2 ^ 59
def prefixEnd_466188 : Nat := 4983230072969 + 3 ^ 40 * 466188 * 2
def baseEnd_466188 : Nat := 106390453048145453780465

theorem tailTrace_466188 : CollatzResearch.WordTrace tailWord_466188 prefixEnd_466188 106390453048145453780465 := by
  unfold tailWord_466188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501636617543984708375609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11335515490058646277834145 8501636617543984708375609)
  ·
    refine ⟨6376227463157988531281707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8501636617543984708375609 6376227463157988531281707)
    ·
      refine ⟨9564341194736982796922561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376227463157988531281707 9564341194736982796922561)
      ·
        refine ⟨7173255896052737097691921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564341194736982796922561 7173255896052737097691921)
        ·
          refine ⟨5379941922039552823268941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7173255896052737097691921 5379941922039552823268941)
          ·
            refine ⟨2017478220764832308725853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5379941922039552823268941 2017478220764832308725853)
            ·
              refine ⟨756554332786812115772195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2017478220764832308725853 756554332786812115772195)
              ·
                refine ⟨1134831499180218173658293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756554332786812115772195 1134831499180218173658293)
                ·
                  refine ⟨106390453048145453780465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134831499180218173658293 106390453048145453780465)
                  ·
                    rfl

theorem cell21_466188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_466188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466188 prefixEnd_466188 := by exact prefixLift 466188
  have htrace : WordTrace (prefixWord ++ tailWord_466188) baseStart_466188 baseEnd_466188 := by
    simpa [prefixWord, tailWord_466188, baseEnd_466188] using wordTrace_append hprefix tailTrace_466188
  have hstable : (prefixWord ++ tailWord_466188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466188).length < 2 ^ (prefixWord ++ tailWord_466188).sum := by decide
  have hdescent : baseEnd_466188 < baseStart_466188 := by decide
  rcases family_descends (prefixWord ++ tailWord_466188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466233 : List Nat := [1, 2, 1, 6, 2, 9]
def baseStart_466233 : Nat := 118140960795 + 466233 * 2 ^ 59
def prefixEnd_466233 : Nat := 4983230072969 + 3 ^ 40 * 466233 * 2
def baseEnd_466233 : Nat := 3940767505971680575199

theorem tailTrace_466233 : CollatzResearch.WordTrace tailWord_466233 prefixEnd_466233 3940767505971680575199 := by
  unfold tailWord_466233
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004914519924942102139353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11336609679949961401426235 17004914519924942102139353)
  ·
    refine ⟨12753685889943706576604515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17004914519924942102139353 12753685889943706576604515)
    ·
      refine ⟨19130528834915559864906773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12753685889943706576604515 19130528834915559864906773)
      ·
        refine ⟨896743539136666868667505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19130528834915559864906773 896743539136666868667505)
        ·
          refine ⟨672557654352500151500629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896743539136666868667505 672557654352500151500629)
          ·
            refine ⟨3940767505971680575199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 672557654352500151500629 3940767505971680575199)
            ·
              rfl

theorem cell21_466233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 9].length) (baseStart_466233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466233 prefixEnd_466233 := by exact prefixLift 466233
  have htrace : WordTrace (prefixWord ++ tailWord_466233) baseStart_466233 baseEnd_466233 := by
    simpa [prefixWord, tailWord_466233, baseEnd_466233] using wordTrace_append hprefix tailTrace_466233
  have hstable : (prefixWord ++ tailWord_466233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466233).length < 2 ^ (prefixWord ++ tailWord_466233).sum := by decide
  have hdescent : baseEnd_466233 < baseStart_466233 := by decide
  rcases family_descends (prefixWord ++ tailWord_466233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466312 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_466312 : Nat := 118140960795 + 466312 * 2 ^ 59
def prefixEnd_466312 : Nat := 4983230072969 + 3 ^ 40 * 466312 * 2
def baseEnd_466312 : Nat := 106418751537548793713545

theorem tailTrace_466312 : CollatzResearch.WordTrace tailWord_466312 prefixEnd_466312 106418751537548793713545 := by
  unfold tailWord_466312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503897943319369297132595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11338530591092492396176793 8503897943319369297132595)
  ·
    refine ⟨12755846914979053945698893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8503897943319369297132595 12755846914979053945698893)
    ·
      refine ⟨4783442593117145229637085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12755846914979053945698893 4783442593117145229637085)
      ·
        refine ⟨1793790972418929461113907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4783442593117145229637085 1793790972418929461113907)
        ·
          refine ⟨2690686458628394191670861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793790972418929461113907 2690686458628394191670861)
          ·
            refine ⟨1009007421985647821876573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2690686458628394191670861 1009007421985647821876573)
            ·
              refine ⟨378377783244617933203715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009007421985647821876573 378377783244617933203715)
              ·
                refine ⟨567566674866926899805573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378377783244617933203715 567566674866926899805573)
                ·
                  refine ⟨106418751537548793713545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567566674866926899805573 106418751537548793713545)
                  ·
                    rfl

theorem cell21_466312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_466312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466312 prefixEnd_466312 := by exact prefixLift 466312
  have htrace : WordTrace (prefixWord ++ tailWord_466312) baseStart_466312 baseEnd_466312 := by
    simpa [prefixWord, tailWord_466312, baseEnd_466312] using wordTrace_append hprefix tailTrace_466312
  have hstable : (prefixWord ++ tailWord_466312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466312).length < 2 ^ (prefixWord ++ tailWord_466312).sum := by decide
  have hdescent : baseEnd_466312 < baseStart_466312 := by decide
  rcases family_descends (prefixWord ++ tailWord_466312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466332 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_466332 : Nat := 118140960795 + 466332 * 2 ^ 59
def prefixEnd_466332 : Nat := 4983230072969 + 3 ^ 40 * 466332 * 2
def baseEnd_466332 : Nat := 106423315810033203380171

theorem tailTrace_466332 : CollatzResearch.WordTrace tailWord_466332 prefixEnd_466332 106423315810033203380171 := by
  unfold tailWord_466332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504262673283141004996625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11339016897710854673328833 8504262673283141004996625)
  ·
    refine ⟨6378197004962355753747469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8504262673283141004996625 6378197004962355753747469)
    ·
      refine ⟨2391823876860883407655301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6378197004962355753747469 2391823876860883407655301)
      ·
        refine ⟨448466976911415638935369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2391823876860883407655301 448466976911415638935369)
        ·
          refine ⟨336350232683561729201527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448466976911415638935369 336350232683561729201527)
          ·
            refine ⟨504525349025342593802291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336350232683561729201527 504525349025342593802291)
            ·
              refine ⟨756788023538013890703437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504525349025342593802291 756788023538013890703437)
              ·
                refine ⟨283795508826755209013789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756788023538013890703437 283795508826755209013789)
                ·
                  refine ⟨106423315810033203380171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283795508826755209013789 106423315810033203380171)
                  ·
                    rfl

theorem cell21_466332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_466332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466332 prefixEnd_466332 := by exact prefixLift 466332
  have htrace : WordTrace (prefixWord ++ tailWord_466332) baseStart_466332 baseEnd_466332 := by
    simpa [prefixWord, tailWord_466332, baseEnd_466332] using wordTrace_append hprefix tailTrace_466332
  have hstable : (prefixWord ++ tailWord_466332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466332).length < 2 ^ (prefixWord ++ tailWord_466332).sum := by decide
  have hdescent : baseEnd_466332 < baseStart_466332 := by decide
  rcases family_descends (prefixWord ++ tailWord_466332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466357 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_466357 : Nat := 118140960795 + 466357 * 2 ^ 59
def prefixEnd_466357 : Nat := 4983230072969 + 3 ^ 40 * 466357 * 2
def baseEnd_466357 : Nat := 106429021150638715463453

theorem tailTrace_466357 : CollatzResearch.WordTrace tailWord_466357 prefixEnd_466357 106429021150638715463453 := by
  unfold tailWord_466357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009437171475711279653325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11339624780983807519768883 17009437171475711279653325)
  ·
    refine ⟨6378538939303391729869997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17009437171475711279653325 6378538939303391729869997)
    ·
      refine ⟨2391952102238771898701249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6378538939303391729869997 2391952102238771898701249)
      ·
        refine ⟨1793964076679078924025937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2391952102238771898701249 1793964076679078924025937)
        ·
          refine ⟨1345473057509309193019453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793964076679078924025937 1345473057509309193019453)
          ·
            refine ⟨504552396565990947382295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345473057509309193019453 504552396565990947382295)
            ·
              refine ⟨756828594848986421073443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504552396565990947382295 756828594848986421073443)
              ·
                refine ⟨1135242892273479631610165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756828594848986421073443 1135242892273479631610165)
                ·
                  refine ⟨106429021150638715463453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135242892273479631610165 106429021150638715463453)
                  ·
                    rfl

theorem cell21_466357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_466357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466357 prefixEnd_466357 := by exact prefixLift 466357
  have htrace : WordTrace (prefixWord ++ tailWord_466357) baseStart_466357 baseEnd_466357 := by
    simpa [prefixWord, tailWord_466357, baseEnd_466357] using wordTrace_append hprefix tailTrace_466357
  have hstable : (prefixWord ++ tailWord_466357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466357).length < 2 ^ (prefixWord ++ tailWord_466357).sum := by decide
  have hdescent : baseEnd_466357 < baseStart_466357 := by decide
  rcases family_descends (prefixWord ++ tailWord_466357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466368 : List Nat := [2, 1, 1, 2, 3, 1, 3, 8]
def baseStart_466368 : Nat := 118140960795 + 466368 * 2 ^ 59
def prefixEnd_466368 : Nat := 4983230072969 + 3 ^ 40 * 466368 * 2
def baseEnd_466368 : Nat := 35477177166835046926699

theorem tailTrace_466368 : CollatzResearch.WordTrace tailWord_466368 prefixEnd_466368 35477177166835046926699 := by
  unfold tailWord_466368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504919187217930079151879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11339892249623906772202505 8504919187217930079151879)
  ·
    refine ⟨12757378780826895118727819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504919187217930079151879 12757378780826895118727819)
    ·
      refine ⟨19136068171240342678091729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757378780826895118727819 19136068171240342678091729)
      ·
        refine ⟨14352051128430257008568797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19136068171240342678091729 14352051128430257008568797)
        ·
          refine ⟨5382019173161346378213299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14352051128430257008568797 5382019173161346378213299)
          ·
            refine ⟨8073028759742019567319949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382019173161346378213299 8073028759742019567319949)
            ·
              refine ⟨3027385784903257337744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8073028759742019567319949 3027385784903257337744981)
              ·
                refine ⟨35477177166835046926699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3027385784903257337744981 35477177166835046926699)
                ·
                  rfl

theorem cell21_466368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_466368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466368 prefixEnd_466368 := by exact prefixLift 466368
  have htrace : WordTrace (prefixWord ++ tailWord_466368) baseStart_466368 baseEnd_466368 := by
    simpa [prefixWord, tailWord_466368, baseEnd_466368] using wordTrace_append hprefix tailTrace_466368
  have hstable : (prefixWord ++ tailWord_466368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466368).length < 2 ^ (prefixWord ++ tailWord_466368).sum := by decide
  have hdescent : baseEnd_466368 < baseStart_466368 := by decide
  rcases family_descends (prefixWord ++ tailWord_466368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466371 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 4]
def baseStart_466371 : Nat := 118140960795 + 466371 * 2 ^ 59
def prefixEnd_466371 : Nat := 4983230072969 + 3 ^ 40 * 466371 * 2
def baseEnd_466371 : Nat := 106432216141377802230091

theorem tailTrace_466371 : CollatzResearch.WordTrace tailWord_466371 prefixEnd_466371 106432216141377802230091 := by
  unfold tailWord_466371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009947793424991670662967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11339965195616661113775311 17009947793424991670662967)
  ·
    refine ⟨25514921690137487505994451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17009947793424991670662967 25514921690137487505994451)
    ·
      refine ⟨38272382535206231258991677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25514921690137487505994451 38272382535206231258991677)
      ·
        refine ⟨14352143450702336722121879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38272382535206231258991677 14352143450702336722121879)
        ·
          refine ⟨21528215176053505083182819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352143450702336722121879 21528215176053505083182819)
          ·
            refine ⟨32292322764080257624774229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21528215176053505083182819 32292322764080257624774229)
            ·
              refine ⟨378425657391565519040323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 32292322764080257624774229 378425657391565519040323)
              ·
                refine ⟨567638486087348278560485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378425657391565519040323 567638486087348278560485)
                ·
                  refine ⟨106432216141377802230091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567638486087348278560485 106432216141377802230091)
                  ·
                    rfl

theorem cell21_466371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_466371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466371 prefixEnd_466371 := by exact prefixLift 466371
  have htrace : WordTrace (prefixWord ++ tailWord_466371) baseStart_466371 baseEnd_466371 := by
    simpa [prefixWord, tailWord_466371, baseEnd_466371] using wordTrace_append hprefix tailTrace_466371
  have hstable : (prefixWord ++ tailWord_466371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466371).length < 2 ^ (prefixWord ++ tailWord_466371).sum := by decide
  have hdescent : baseEnd_466371 < baseStart_466371 := by decide
  rcases family_descends (prefixWord ++ tailWord_466371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466464 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_466464 : Nat := 118140960795 + 466464 * 2 ^ 59
def prefixEnd_466464 : Nat := 4983230072969 + 3 ^ 40 * 466464 * 2
def baseEnd_466464 : Nat := 106453440008430307179901

theorem tailTrace_466464 : CollatzResearch.WordTrace tailWord_466464 prefixEnd_466464 106453440008430307179901 := by
  unfold tailWord_466464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506669891044034276899223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11342226521392045702532297 8506669891044034276899223)
  ·
    refine ⟨12760004836566051415348835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506669891044034276899223 12760004836566051415348835)
    ·
      refine ⟨19140007254849077123023253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12760004836566051415348835 19140007254849077123023253)
      ·
        refine ⟨897187840071050490141715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19140007254849077123023253 897187840071050490141715)
        ·
          refine ⟨1345781760106575735212573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897187840071050490141715 1345781760106575735212573)
          ·
            refine ⟨504668160039965900704715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345781760106575735212573 504668160039965900704715)
            ·
              refine ⟨757002240059948851057073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504668160039965900704715 757002240059948851057073)
              ·
                refine ⟨567751680044961638292805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757002240059948851057073 567751680044961638292805)
                ·
                  refine ⟨106453440008430307179901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567751680044961638292805 106453440008430307179901)
                  ·
                    rfl

theorem cell21_466464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_466464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466464 prefixEnd_466464 := by exact prefixLift 466464
  have htrace : WordTrace (prefixWord ++ tailWord_466464) baseStart_466464 baseEnd_466464 := by
    simpa [prefixWord, tailWord_466464, baseEnd_466464] using wordTrace_append hprefix tailTrace_466464
  have hstable : (prefixWord ++ tailWord_466464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466464).length < 2 ^ (prefixWord ++ tailWord_466464).sum := by decide
  have hdescent : baseEnd_466464 < baseStart_466464 := by decide
  rcases family_descends (prefixWord ++ tailWord_466464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466644 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_466644 : Nat := 118140960795 + 466644 * 2 ^ 59
def prefixEnd_466644 : Nat := 4983230072969 + 3 ^ 40 * 466644 * 2
def baseEnd_466644 : Nat := 106494518460789994179533

theorem tailTrace_466644 : CollatzResearch.WordTrace tailWord_466644 prefixEnd_466644 106494518460789994179533 := by
  unfold tailWord_466644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509952460717979647675493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11346603280957306196900657 8509952460717979647675493)
  ·
    refine ⟨1595616086384621183939155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8509952460717979647675493 1595616086384621183939155)
    ·
      refine ⟨2393424129576931775908733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595616086384621183939155 2393424129576931775908733)
      ·
        refine ⟨897534048591349415965775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2393424129576931775908733 897534048591349415965775)
        ·
          refine ⟨1346301072887024123948663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897534048591349415965775 1346301072887024123948663)
          ·
            refine ⟨2019451609330536185922995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346301072887024123948663 2019451609330536185922995)
            ·
              refine ⟨3029177413995804278884493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019451609330536185922995 3029177413995804278884493)
              ·
                refine ⟨1135941530248426604581685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029177413995804278884493 1135941530248426604581685)
                ·
                  refine ⟨106494518460789994179533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135941530248426604581685 106494518460789994179533)
                  ·
                    rfl

theorem cell21_466644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_466644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466644 prefixEnd_466644 := by exact prefixLift 466644
  have htrace : WordTrace (prefixWord ++ tailWord_466644) baseStart_466644 baseEnd_466644 := by
    simpa [prefixWord, tailWord_466644, baseEnd_466644] using wordTrace_append hprefix tailTrace_466644
  have hstable : (prefixWord ++ tailWord_466644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466644).length < 2 ^ (prefixWord ++ tailWord_466644).sum := by decide
  have hdescent : baseEnd_466644 < baseStart_466644 := by decide
  rcases family_descends (prefixWord ++ tailWord_466644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466678 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_466678 : Nat := 118140960795 + 466678 * 2 ^ 59
def prefixEnd_466678 : Nat := 4983230072969 + 3 ^ 40 * 466678 * 2
def baseEnd_466678 : Nat := 106502277724013490612797

theorem tailTrace_466678 : CollatzResearch.WordTrace tailWord_466678 prefixEnd_466678 106502277724013490612797 := by
  unfold tailWord_466678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063821562707048943880543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11347430002208522068059125 1063821562707048943880543)
  ·
    refine ⟨1595732344060573415820815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063821562707048943880543 1595732344060573415820815)
    ·
      refine ⟨2393598516090860123731223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595732344060573415820815 2393598516090860123731223)
      ·
        refine ⟨3590397774136290185596835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393598516090860123731223 3590397774136290185596835)
        ·
          refine ⟨5385596661204435278395253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590397774136290185596835 5385596661204435278395253)
          ·
            refine ⟨504899686987915807349555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5385596661204435278395253 504899686987915807349555)
            ·
              refine ⟨757349530481873711024333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504899686987915807349555 757349530481873711024333)
              ·
                refine ⟨284006073930702641634125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757349530481873711024333 284006073930702641634125)
                ·
                  refine ⟨106502277724013490612797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284006073930702641634125 106502277724013490612797)
                  ·
                    rfl

theorem cell21_466678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_466678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466678 prefixEnd_466678 := by exact prefixLift 466678
  have htrace : WordTrace (prefixWord ++ tailWord_466678) baseStart_466678 baseEnd_466678 := by
    simpa [prefixWord, tailWord_466678, baseEnd_466678] using wordTrace_append hprefix tailTrace_466678
  have hstable : (prefixWord ++ tailWord_466678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466678).length < 2 ^ (prefixWord ++ tailWord_466678).sum := by decide
  have hdescent : baseEnd_466678 < baseStart_466678 := by decide
  rcases family_descends (prefixWord ++ tailWord_466678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466706 : List Nat := [3, 2, 4, 1, 1, 2, 2, 6]
def baseStart_466706 : Nat := 118140960795 + 466706 * 2 ^ 59
def prefixEnd_466706 : Nat := 4983230072969 + 3 ^ 40 * 466706 * 2
def baseEnd_466706 : Nat := 35502889235163888048691

theorem tailTrace_466706 : CollatzResearch.WordTrace tailWord_466706 prefixEnd_466706 35502889235163888048691 := by
  unfold tailWord_466706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255541561802835971026993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11348110831474229256071981 4255541561802835971026993)
  ·
    refine ⟨3191656171352126978270245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255541561802835971026993 3191656171352126978270245)
    ·
      refine ⟨598435532128523808425671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3191656171352126978270245 598435532128523808425671)
      ·
        refine ⟨897653298192785712638507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598435532128523808425671 897653298192785712638507)
        ·
          refine ⟨1346479947289178568957761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897653298192785712638507 1346479947289178568957761)
          ·
            refine ⟨1009859960466883926718321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346479947289178568957761 1009859960466883926718321)
            ·
              refine ⟨757394970350162945038741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009859960466883926718321 757394970350162945038741)
              ·
                refine ⟨35502889235163888048691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 757394970350162945038741 35502889235163888048691)
                ·
                  rfl

theorem cell21_466706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_466706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466706 prefixEnd_466706 := by exact prefixLift 466706
  have htrace : WordTrace (prefixWord ++ tailWord_466706) baseStart_466706 baseEnd_466706 := by
    simpa [prefixWord, tailWord_466706, baseEnd_466706] using wordTrace_append hprefix tailTrace_466706
  have hstable : (prefixWord ++ tailWord_466706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466706).length < 2 ^ (prefixWord ++ tailWord_466706).sum := by decide
  have hdescent : baseEnd_466706 < baseStart_466706 := by decide
  rcases family_descends (prefixWord ++ tailWord_466706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466751 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_466751 : Nat := 118140960795 + 466751 * 2 ^ 59
def prefixEnd_466751 : Nat := 4983230072969 + 3 ^ 40 * 466751 * 2
def baseEnd_466751 : Nat := 106518937318581585895981

theorem tailTrace_466751 : CollatzResearch.WordTrace tailWord_466751 prefixEnd_466751 106518937318581585895981 := by
  unfold tailWord_466751
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023807532048316569496107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11349205021365544379664071 17023807532048316569496107)
  ·
    refine ⟨25535711298072474854244161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17023807532048316569496107 25535711298072474854244161)
    ·
      refine ⟨19151783473554356140683121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25535711298072474854244161 19151783473554356140683121)
      ·
        refine ⟨14363837605165767105512341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19151783473554356140683121 14363837605165767105512341)
        ·
          refine ⟨673304887742145333070891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14363837605165767105512341 673304887742145333070891)
          ·
            refine ⟨1009957331613217999606337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673304887742145333070891 1009957331613217999606337)
            ·
              refine ⟨757467998709913499704753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009957331613217999606337 757467998709913499704753)
              ·
                refine ⟨568100999032435124778565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757467998709913499704753 568100999032435124778565)
                ·
                  refine ⟨106518937318581585895981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568100999032435124778565 106518937318581585895981)
                  ·
                    rfl

theorem cell21_466751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_466751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466751 prefixEnd_466751 := by exact prefixLift 466751
  have htrace : WordTrace (prefixWord ++ tailWord_466751) baseStart_466751 baseEnd_466751 := by
    simpa [prefixWord, tailWord_466751, baseEnd_466751] using wordTrace_append hprefix tailTrace_466751
  have hstable : (prefixWord ++ tailWord_466751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466751).length < 2 ^ (prefixWord ++ tailWord_466751).sum := by decide
  have hdescent : baseEnd_466751 < baseStart_466751 := by decide
  rcases family_descends (prefixWord ++ tailWord_466751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466796 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_466796 : Nat := 118140960795 + 466796 * 2 ^ 59
def prefixEnd_466796 : Nat := 4983230072969 + 3 ^ 40 * 466796 * 2
def baseEnd_466796 : Nat := 106529206931671507645889

theorem tailTrace_466796 : CollatzResearch.WordTrace tailWord_466796 prefixEnd_466796 106529206931671507645889 := by
  unfold tailWord_466796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512724408442644627442121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11350299211256859503256161 8512724408442644627442121)
  ·
    refine ⟨6384543306331983470581591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8512724408442644627442121 6384543306331983470581591)
    ·
      refine ⟨9576814959497975205872387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384543306331983470581591 9576814959497975205872387)
      ·
        refine ⟨14365222439246962808808581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576814959497975205872387 14365222439246962808808581)
        ·
          refine ⟨2693479207358805526651609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14365222439246962808808581 2693479207358805526651609)
          ·
            refine ⟨2020109405519104144988707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693479207358805526651609 2020109405519104144988707)
            ·
              refine ⟨3030164108278656217483061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020109405519104144988707 3030164108278656217483061)
              ·
                refine ⟨284077885151124020389037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3030164108278656217483061 284077885151124020389037)
                ·
                  refine ⟨106529206931671507645889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284077885151124020389037 106529206931671507645889)
                  ·
                    rfl

theorem cell21_466796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_466796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466796 prefixEnd_466796 := by exact prefixLift 466796
  have htrace : WordTrace (prefixWord ++ tailWord_466796) baseStart_466796 baseEnd_466796 := by
    simpa [prefixWord, tailWord_466796, baseEnd_466796] using wordTrace_append hprefix tailTrace_466796
  have hstable : (prefixWord ++ tailWord_466796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466796).length < 2 ^ (prefixWord ++ tailWord_466796).sum := by decide
  have hdescent : baseEnd_466796 < baseStart_466796 := by decide
  rcases family_descends (prefixWord ++ tailWord_466796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466810 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_466810 : Nat := 118140960795 + 466810 * 2 ^ 59
def prefixEnd_466810 : Nat := 4983230072969 + 3 ^ 40 * 466810 * 2
def baseEnd_466810 : Nat := 106532401922410594412527

theorem tailTrace_466810 : CollatzResearch.WordTrace tailWord_466810 prefixEnd_466810 106532401922410594412527 := by
  unfold tailWord_466810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256489859708642411473471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11350639625889713097262589 4256489859708642411473471)
  ·
    refine ⟨6384734789562963617210207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256489859708642411473471 6384734789562963617210207)
    ·
      refine ⟨9577102184344445425815311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384734789562963617210207 9577102184344445425815311)
      ·
        refine ⟨14365653276516668138722967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9577102184344445425815311 14365653276516668138722967)
        ·
          refine ⟨21548479914775002208084451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14365653276516668138722967 21548479914775002208084451)
          ·
            refine ⟨32322719872162503312126677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21548479914775002208084451 32322719872162503312126677)
            ·
              refine ⟨757563747003808671377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32322719872162503312126677 757563747003808671377969)
              ·
                refine ⟨568172810252856503533477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757563747003808671377969 568172810252856503533477)
                ·
                  refine ⟨106532401922410594412527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568172810252856503533477 106532401922410594412527)
                  ·
                    rfl

theorem cell21_466810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_466810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466810 prefixEnd_466810 := by exact prefixLift 466810
  have htrace : WordTrace (prefixWord ++ tailWord_466810) baseStart_466810 baseEnd_466810 := by
    simpa [prefixWord, tailWord_466810, baseEnd_466810] using wordTrace_append hprefix tailTrace_466810
  have hstable : (prefixWord ++ tailWord_466810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466810).length < 2 ^ (prefixWord ++ tailWord_466810).sum := by decide
  have hdescent : baseEnd_466810 < baseStart_466810 := by decide
  rcases family_descends (prefixWord ++ tailWord_466810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466900 : List Nat := [2, 4, 1, 2, 1, 1, 1, 9]
def baseStart_466900 : Nat := 118140960795 + 466900 * 2 ^ 59
def prefixEnd_466900 : Nat := 4983230072969 + 3 ^ 40 * 466900 * 2
def baseEnd_466900 : Nat := 35517647049530145970781

theorem tailTrace_466900 : CollatzResearch.WordTrace tailWord_466900 prefixEnd_466900 35517647049530145970781 := by
  unfold tailWord_466900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514621004254257508335077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11352828005672343344446769 8514621004254257508335077)
  ·
    refine ⟨1596491438297673282812827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8514621004254257508335077 1596491438297673282812827)
    ·
      refine ⟨2394737157446509924219241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596491438297673282812827 2394737157446509924219241)
      ·
        refine ⟨1796052868084882443164431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394737157446509924219241 1796052868084882443164431)
        ·
          refine ⟨2694079302127323664746647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796052868084882443164431 2694079302127323664746647)
          ·
            refine ⟨4041118953190985497119971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694079302127323664746647 4041118953190985497119971)
            ·
              refine ⟨6061678429786478245679957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041118953190985497119971 6061678429786478245679957)
              ·
                refine ⟨35517647049530145970781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6061678429786478245679957 35517647049530145970781)
                ·
                  rfl

theorem cell21_466900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_466900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466900 prefixEnd_466900 := by exact prefixLift 466900
  have htrace : WordTrace (prefixWord ++ tailWord_466900) baseStart_466900 baseEnd_466900 := by
    simpa [prefixWord, tailWord_466900, baseEnd_466900] using wordTrace_append hprefix tailTrace_466900
  have hstable : (prefixWord ++ tailWord_466900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466900).length < 2 ^ (prefixWord ++ tailWord_466900).sum := by decide
  have hdescent : baseEnd_466900 < baseStart_466900 := by decide
  rcases family_descends (prefixWord ++ tailWord_466900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466934 : List Nat := [5, 1, 1, 1, 4, 2, 1, 6]
def baseStart_466934 : Nat := 118140960795 + 466934 * 2 ^ 59
def prefixEnd_466934 : Nat := 4983230072969 + 3 ^ 40 * 466934 * 2
def baseEnd_466934 : Nat := 35520233470604644781869

theorem tailTrace_466934 : CollatzResearch.WordTrace tailWord_466934 prefixEnd_466934 35520233470604644781869 := by
  unfold tailWord_466934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064405130649083676462991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11353654726923559215605237 1064405130649083676462991)
  ·
    refine ⟨1596607695973625514694487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1064405130649083676462991 1596607695973625514694487)
    ·
      refine ⟨2394911543960438272041731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596607695973625514694487 2394911543960438272041731)
      ·
        refine ⟨3592367315940657408062597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394911543960438272041731 3592367315940657408062597)
        ·
          refine ⟨673568871738873264011737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3592367315940657408062597 673568871738873264011737)
          ·
            refine ⟨505176653804154948008803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673568871738873264011737 505176653804154948008803)
            ·
              refine ⟨757764980706232422013205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505176653804154948008803 757764980706232422013205)
              ·
                refine ⟨35520233470604644781869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 757764980706232422013205 35520233470604644781869)
                ·
                  rfl

theorem cell21_466934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_466934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466934 prefixEnd_466934 := by exact prefixLift 466934
  have htrace : WordTrace (prefixWord ++ tailWord_466934) baseStart_466934 baseEnd_466934 := by
    simpa [prefixWord, tailWord_466934, baseEnd_466934] using wordTrace_append hprefix tailTrace_466934
  have hstable : (prefixWord ++ tailWord_466934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466934).length < 2 ^ (prefixWord ++ tailWord_466934).sum := by decide
  have hdescent : baseEnd_466934 < baseStart_466934 := by decide
  rcases family_descends (prefixWord ++ tailWord_466934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466965 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 3]
def baseStart_466965 : Nat := 118140960795 + 466965 * 2 ^ 59
def prefixEnd_466965 : Nat := 4983230072969 + 3 ^ 40 * 466965 * 2
def baseEnd_466965 : Nat := 106567775034164769328877

theorem tailTrace_466965 : CollatzResearch.WordTrace tailWord_466965 prefixEnd_466965 106567775034164769328877 := by
  unfold tailWord_466965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031612753273031117786349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11354408502182020745190899 17031612753273031117786349)
  ·
    refine ⟨6386854782477386669169881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17031612753273031117786349 6386854782477386669169881)
    ·
      refine ⟨4790141086858040001877411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6386854782477386669169881 4790141086858040001877411)
      ·
        refine ⟨7185211630287060002816117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790141086858040001877411 7185211630287060002816117)
        ·
          refine ⟨673613590339411875264011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7185211630287060002816117 673613590339411875264011)
          ·
            refine ⟨1010420385509117812896017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673613590339411875264011 1010420385509117812896017)
            ·
              refine ⟨757815289131838359672013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010420385509117812896017 757815289131838359672013)
              ·
                refine ⟨284180733424439384877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757815289131838359672013 284180733424439384877005)
                ·
                  refine ⟨106567775034164769328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284180733424439384877005 106567775034164769328877)
                  ·
                    rfl

theorem cell21_466965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_466965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466965 prefixEnd_466965 := by exact prefixLift 466965
  have htrace : WordTrace (prefixWord ++ tailWord_466965) baseStart_466965 baseEnd_466965 := by
    simpa [prefixWord, tailWord_466965, baseEnd_466965] using wordTrace_append hprefix tailTrace_466965
  have hstable : (prefixWord ++ tailWord_466965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466965).length < 2 ^ (prefixWord ++ tailWord_466965).sum := by decide
  have hdescent : baseEnd_466965 < baseStart_466965 := by decide
  rcases family_descends (prefixWord ++ tailWord_466965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467052 : List Nat := [2, 2, 1, 1, 3, 4, 2, 6]
def baseStart_467052 : Nat := 118140960795 + 467052 * 2 ^ 59
def prefixEnd_467052 : Nat := 4983230072969 + 3 ^ 40 * 467052 * 2
def baseEnd_467052 : Nat := 35529209873157317126233

theorem tailTrace_467052 : CollatzResearch.WordTrace tailWord_467052 prefixEnd_467052 35529209873157317126233 := by
  unfold tailWord_467052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517392951978922488101705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11356523935971896650802273 8517392951978922488101705)
  ·
    refine ⟨6388044713984191866076279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8517392951978922488101705 6388044713984191866076279)
    ·
      refine ⟨9582067070976287799114419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388044713984191866076279 9582067070976287799114419)
      ·
        refine ⟨14373100606464431698671629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9582067070976287799114419 14373100606464431698671629)
        ·
          refine ⟨5389912727424161887001861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14373100606464431698671629 5389912727424161887001861)
          ·
            refine ⟨1010608636392030353812849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5389912727424161887001861 1010608636392030353812849)
            ·
              refine ⟨757956477294022765359637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010608636392030353812849 757956477294022765359637)
              ·
                refine ⟨35529209873157317126233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 757956477294022765359637 35529209873157317126233)
                ·
                  rfl

theorem cell21_467052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_467052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467052 prefixEnd_467052 := by exact prefixLift 467052
  have htrace : WordTrace (prefixWord ++ tailWord_467052) baseStart_467052 baseEnd_467052 := by
    simpa [prefixWord, tailWord_467052, baseEnd_467052] using wordTrace_append hprefix tailTrace_467052
  have hstable : (prefixWord ++ tailWord_467052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467052).length < 2 ^ (prefixWord ++ tailWord_467052).sum := by decide
  have hdescent : baseEnd_467052 < baseStart_467052 := by decide
  rcases family_descends (prefixWord ++ tailWord_467052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467055 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 4]
def baseStart_467055 : Nat := 118140960795 + 467055 * 2 ^ 59
def prefixEnd_467055 : Nat := 4983230072969 + 3 ^ 40 * 467055 * 2
def baseEnd_467055 : Nat := 106588314260344612828693

theorem tailTrace_467055 : CollatzResearch.WordTrace tailWord_467055 prefixEnd_467055 106588314260344612828693 := by
  unfold tailWord_467055
  simp only [CollatzResearch.WordTrace]
  refine ⟨17034895322946976488562619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11356596881964650992375079 17034895322946976488562619)
  ·
    refine ⟨25552342984420464732843929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17034895322946976488562619 25552342984420464732843929)
    ·
      refine ⟨19164257238315348549632947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25552342984420464732843929 19164257238315348549632947)
      ·
        refine ⟨28746385857473022824449421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19164257238315348549632947 28746385857473022824449421)
        ·
          refine ⟨10779894696552383559168533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28746385857473022824449421 10779894696552383559168533)
          ·
            refine ⟨505307563900892979336025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10779894696552383559168533 505307563900892979336025)
            ·
              refine ⟨378980672925669734502019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505307563900892979336025 378980672925669734502019)
              ·
                refine ⟨568471009388504601753029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378980672925669734502019 568471009388504601753029)
                ·
                  refine ⟨106588314260344612828693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568471009388504601753029 106588314260344612828693)
                  ·
                    rfl

theorem cell21_467055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_467055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467055 prefixEnd_467055 := by exact prefixLift 467055
  have htrace : WordTrace (prefixWord ++ tailWord_467055) baseStart_467055 baseEnd_467055 := by
    simpa [prefixWord, tailWord_467055, baseEnd_467055] using wordTrace_append hprefix tailTrace_467055
  have hstable : (prefixWord ++ tailWord_467055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467055).length < 2 ^ (prefixWord ++ tailWord_467055).sum := by decide
  have hdescent : baseEnd_467055 < baseStart_467055 := by decide
  rcases family_descends (prefixWord ++ tailWord_467055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467092 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_467092 : Nat := 118140960795 + 467092 * 2 ^ 59
def prefixEnd_467092 : Nat := 4983230072969 + 3 ^ 40 * 467092 * 2
def baseEnd_467092 : Nat := 106596758164440770711951

theorem tailTrace_467092 : CollatzResearch.WordTrace tailWord_467092 prefixEnd_467092 106596758164440770711951 := by
  unfold tailWord_467092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518122411906465903829765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11357496549208621205106353 8518122411906465903829765)
  ·
    refine ⟨1597147952232462356968081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8518122411906465903829765 1597147952232462356968081)
    ·
      refine ⟨1197860964174346767726061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1597147952232462356968081 1197860964174346767726061)
      ·
        refine ⟨449197861565380037897273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1197860964174346767726061 449197861565380037897273)
        ·
          refine ⟨336898396174035028422955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449197861565380037897273 336898396174035028422955)
          ·
            refine ⟨505347594261052542634433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336898396174035028422955 505347594261052542634433)
            ·
              refine ⟨379010695695789406975825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505347594261052542634433 379010695695789406975825)
              ·
                refine ⟨284258021771842055231869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379010695695789406975825 284258021771842055231869)
                ·
                  refine ⟨106596758164440770711951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284258021771842055231869 106596758164440770711951)
                  ·
                    rfl

theorem cell21_467092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_467092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467092 prefixEnd_467092 := by exact prefixLift 467092
  have htrace : WordTrace (prefixWord ++ tailWord_467092) baseStart_467092 baseEnd_467092 := by
    simpa [prefixWord, tailWord_467092, baseEnd_467092] using wordTrace_append hprefix tailTrace_467092
  have hstable : (prefixWord ++ tailWord_467092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467092).length < 2 ^ (prefixWord ++ tailWord_467092).sum := by decide
  have hdescent : baseEnd_467092 < baseStart_467092 := by decide
  rcases family_descends (prefixWord ++ tailWord_467092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467100 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_467100 : Nat := 118140960795 + 467100 * 2 ^ 59
def prefixEnd_467100 : Nat := 4983230072969 + 3 ^ 40 * 467100 * 2
def baseEnd_467100 : Nat := 106598583873434534578601

theorem tailTrace_467100 : CollatzResearch.WordTrace tailWord_467100 prefixEnd_467100 106598583873434534578601 := by
  unfold tailWord_467100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518268303891974586975377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11357691071855966115967169 8518268303891974586975377)
  ·
    refine ⟨6388701227918980940231533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8518268303891974586975377 6388701227918980940231533)
    ·
      refine ⟨2395762960469617852586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6388701227918980940231533 2395762960469617852586825)
      ·
        refine ⟨1796822220352213389440119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2395762960469617852586825 1796822220352213389440119)
        ·
          refine ⟨2695233330528320084160179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796822220352213389440119 2695233330528320084160179)
          ·
            refine ⟨4042849995792480126240269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695233330528320084160179 4042849995792480126240269)
            ·
              refine ⟨1516068748422180047340101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042849995792480126240269 1516068748422180047340101)
              ·
                refine ⟨284262890329158758876269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1516068748422180047340101 284262890329158758876269)
                ·
                  refine ⟨106598583873434534578601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284262890329158758876269 106598583873434534578601)
                  ·
                    rfl

theorem cell21_467100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_467100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467100 prefixEnd_467100 := by exact prefixLift 467100
  have htrace : WordTrace (prefixWord ++ tailWord_467100) baseStart_467100 baseEnd_467100 := by
    simpa [prefixWord, tailWord_467100, baseEnd_467100] using wordTrace_append hprefix tailTrace_467100
  have hstable : (prefixWord ++ tailWord_467100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467100).length < 2 ^ (prefixWord ++ tailWord_467100).sum := by decide
  have hdescent : baseEnd_467100 < baseStart_467100 := by decide
  rcases family_descends (prefixWord ++ tailWord_467100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467128 : List Nat := [2, 1, 2, 1, 2, 1, 7, 5]
def baseStart_467128 : Nat := 118140960795 + 467128 * 2 ^ 59
def prefixEnd_467128 : Nat := 4983230072969 + 3 ^ 40 * 467128 * 2
def baseEnd_467128 : Nat := 35534991284970902703959

theorem tailTrace_467128 : CollatzResearch.WordTrace tailWord_467128 prefixEnd_467128 35534991284970902703959 := by
  unfold tailWord_467128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518778925841254977985019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11358371901121673303980025 8518778925841254977985019)
  ·
    refine ⟨12778168388761882466977529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518778925841254977985019 12778168388761882466977529)
    ·
      refine ⟨9583626291571411850233147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12778168388761882466977529 9583626291571411850233147)
      ·
        refine ⟨14375439437357117775349721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583626291571411850233147 14375439437357117775349721)
        ·
          refine ⟨10781579578017838331512291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14375439437357117775349721 10781579578017838331512291)
          ·
            refine ⟨16172369367026757497268437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10781579578017838331512291 16172369367026757497268437)
            ·
              refine ⟨379039907039689628842229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16172369367026757497268437 379039907039689628842229)
              ·
                refine ⟨35534991284970902703959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379039907039689628842229 35534991284970902703959)
                ·
                  rfl

theorem cell21_467128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_467128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467128 prefixEnd_467128 := by exact prefixLift 467128
  have htrace : WordTrace (prefixWord ++ tailWord_467128) baseStart_467128 baseEnd_467128 := by
    simpa [prefixWord, tailWord_467128, baseEnd_467128] using wordTrace_append hprefix tailTrace_467128
  have hstable : (prefixWord ++ tailWord_467128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467128).length < 2 ^ (prefixWord ++ tailWord_467128).sum := by decide
  have hdescent : baseEnd_467128 < baseStart_467128 := by decide
  rcases family_descends (prefixWord ++ tailWord_467128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467148 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_467148 : Nat := 118140960795 + 467148 * 2 ^ 59
def prefixEnd_467148 : Nat := 4983230072969 + 3 ^ 40 * 467148 * 2
def baseEnd_467148 : Nat := 106609538127397117778503

theorem tailTrace_467148 : CollatzResearch.WordTrace tailWord_467148 prefixEnd_467148 106609538127397117778503 := by
  unfold tailWord_467148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519143655805026685849049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11358858207740035581132065 8519143655805026685849049)
  ·
    refine ⟨6389357741853770014386787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8519143655805026685849049 6389357741853770014386787)
    ·
      refine ⟨9584036612780655021580181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389357741853770014386787 9584036612780655021580181)
      ·
        refine ⟨449251716224093204136571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9584036612780655021580181 449251716224093204136571)
        ·
          refine ⟨673877574336139806204857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449251716224093204136571 673877574336139806204857)
          ·
            refine ⟨505408180752104854653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673877574336139806204857 505408180752104854653643)
            ·
              refine ⟨758112271128157281980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505408180752104854653643 758112271128157281980465)
              ·
                refine ⟨568584203346117961485349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758112271128157281980465 568584203346117961485349)
                ·
                  refine ⟨106609538127397117778503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568584203346117961485349 106609538127397117778503)
                  ·
                    rfl

theorem cell21_467148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_467148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467148 prefixEnd_467148 := by exact prefixLift 467148
  have htrace : WordTrace (prefixWord ++ tailWord_467148) baseStart_467148 baseEnd_467148 := by
    simpa [prefixWord, tailWord_467148, baseEnd_467148] using wordTrace_append hprefix tailTrace_467148
  have hstable : (prefixWord ++ tailWord_467148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467148).length < 2 ^ (prefixWord ++ tailWord_467148).sum := by decide
  have hdescent : baseEnd_467148 < baseStart_467148 := by decide
  rcases family_descends (prefixWord ++ tailWord_467148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467187 : List Nat := [1, 1, 1, 2, 2, 4, 3, 7]
def baseStart_467187 : Nat := 118140960795 + 467187 * 2 ^ 59
def prefixEnd_467187 : Nat := 4983230072969 + 3 ^ 40 * 467187 * 2
def baseEnd_467187 : Nat := 35539479486247238876141

theorem tailTrace_467187 : CollatzResearch.WordTrace tailWord_467187 prefixEnd_467187 35539479486247238876141 := by
  unfold tailWord_467187
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039709758468763032367815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359806505645842021578543 17039709758468763032367815)
  ·
    refine ⟨25559564637703144548551723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039709758468763032367815 25559564637703144548551723)
    ·
      refine ⟨38339346956554716822827585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25559564637703144548551723 38339346956554716822827585)
      ·
        refine ⟨28754510217416037617120689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38339346956554716822827585 28754510217416037617120689)
        ·
          refine ⟨21565882663062028212840517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28754510217416037617120689 21565882663062028212840517)
          ·
            refine ⟨4043602999324130289907597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21565882663062028212840517 4043602999324130289907597)
            ·
              refine ⟨1516351124746548858715349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4043602999324130289907597 1516351124746548858715349)
              ·
                refine ⟨35539479486247238876141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1516351124746548858715349 35539479486247238876141)
                ·
                  rfl

theorem cell21_467187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_467187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467187 prefixEnd_467187 := by exact prefixLift 467187
  have htrace : WordTrace (prefixWord ++ tailWord_467187) baseStart_467187 baseEnd_467187 := by
    simpa [prefixWord, tailWord_467187, baseEnd_467187] using wordTrace_append hprefix tailTrace_467187
  have hstable : (prefixWord ++ tailWord_467187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467187).length < 2 ^ (prefixWord ++ tailWord_467187).sum := by decide
  have hdescent : baseEnd_467187 < baseStart_467187 := by decide
  rcases family_descends (prefixWord ++ tailWord_467187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467280 : List Nat := [2, 1, 1, 1, 1, 8, 1, 6]
def baseStart_467280 : Nat := 118140960795 + 467280 * 2 ^ 59
def prefixEnd_467280 : Nat := 4983230072969 + 3 ^ 40 * 467280 * 2
def baseEnd_467280 : Nat := 35546554108598073859411

theorem tailTrace_467280 : CollatzResearch.WordTrace tailWord_467280 prefixEnd_467280 35546554108598073859411 := by
  unfold tailWord_467280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8521550873565919957751647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11362067831421226610335529 8521550873565919957751647)
  ·
    refine ⟨12782326310348879936627471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8521550873565919957751647 12782326310348879936627471)
    ·
      refine ⟨19173489465523319904941207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12782326310348879936627471 19173489465523319904941207)
      ·
        refine ⟨28760234198284979857411811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19173489465523319904941207 28760234198284979857411811)
        ·
          refine ⟨43140351297427469786117717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760234198284979857411811 43140351297427469786117717)
          ·
            refine ⟨505550991766728161556067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43140351297427469786117717 505550991766728161556067)
            ·
              refine ⟨758326487650092242334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505550991766728161556067 758326487650092242334101)
              ·
                refine ⟨35546554108598073859411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 758326487650092242334101 35546554108598073859411)
                ·
                  rfl

theorem cell21_467280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_467280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467280 prefixEnd_467280 := by exact prefixLift 467280
  have htrace : WordTrace (prefixWord ++ tailWord_467280) baseStart_467280 baseEnd_467280 := by
    simpa [prefixWord, tailWord_467280, baseEnd_467280] using wordTrace_append hprefix tailTrace_467280
  have hstable : (prefixWord ++ tailWord_467280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467280).length < 2 ^ (prefixWord ++ tailWord_467280).sum := by decide
  have hdescent : baseEnd_467280 < baseStart_467280 := by decide
  rcases family_descends (prefixWord ++ tailWord_467280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467325 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_467325 : Nat := 118140960795 + 467325 * 2 ^ 59
def prefixEnd_467325 : Nat := 4983230072969 + 3 ^ 40 * 467325 * 2
def baseEnd_467325 : Nat := 106649931938884143328141

theorem tailTrace_467325 : CollatzResearch.WordTrace tailWord_467325 prefixEnd_467325 106649931938884143328141 := by
  unfold tailWord_467325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044743031968812600891429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11363162021312541733927619 17044743031968812600891429)
  ·
    refine ⟨3195889318494152362667143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17044743031968812600891429 3195889318494152362667143)
    ·
      refine ⟨4793833977741228544000715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195889318494152362667143 4793833977741228544000715)
      ·
        refine ⟨7190750966611842816001073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793833977741228544000715 7190750966611842816001073)
        ·
          refine ⟨5393063224958882112000805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7190750966611842816001073 5393063224958882112000805)
          ·
            refine ⟨1011199354679790396000151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5393063224958882112000805 1011199354679790396000151)
            ·
              refine ⟨1516799032019685594000227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011199354679790396000151 1516799032019685594000227)
              ·
                refine ⟨2275198548029528391000341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516799032019685594000227 2275198548029528391000341)
                ·
                  refine ⟨106649931938884143328141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2275198548029528391000341 106649931938884143328141)
                  ·
                    rfl

theorem cell21_467325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_467325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467325 prefixEnd_467325 := by exact prefixLift 467325
  have htrace : WordTrace (prefixWord ++ tailWord_467325) baseStart_467325 baseEnd_467325 := by
    simpa [prefixWord, tailWord_467325, baseEnd_467325] using wordTrace_append hprefix tailTrace_467325
  have hstable : (prefixWord ++ tailWord_467325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467325).length < 2 ^ (prefixWord ++ tailWord_467325).sum := by decide
  have hdescent : baseEnd_467325 < baseStart_467325 := by decide
  rcases family_descends (prefixWord ++ tailWord_467325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467373 : List Nat := [1, 5, 2, 2, 2, 2, 7]
def baseStart_467373 : Nat := 118140960795 + 467373 * 2 ^ 59
def prefixEnd_467373 : Nat := 4983230072969 + 3 ^ 40 * 467373 * 2
def baseEnd_467373 : Nat := 11851209576982969614227

theorem tailTrace_467373 : CollatzResearch.WordTrace tailWord_467373 prefixEnd_467373 11851209576982969614227 := by
  unfold tailWord_467373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046493735794916798638773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11364329157196611199092515 17046493735794916798638773)
  ·
    refine ⟨1598108787730773449872385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17046493735794916798638773 1598108787730773449872385)
    ·
      refine ⟨1198581590798080087404289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598108787730773449872385 1198581590798080087404289)
      ·
        refine ⟨898936193098560065553217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1198581590798080087404289 898936193098560065553217)
        ·
          refine ⟨674202144823920049164913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898936193098560065553217 674202144823920049164913)
          ·
            refine ⟨505651608617940036873685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674202144823920049164913 505651608617940036873685)
            ·
              refine ⟨11851209576982969614227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 505651608617940036873685 11851209576982969614227)
              ·
                rfl

theorem cell21_467373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 7].length) (baseStart_467373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467373 prefixEnd_467373 := by exact prefixLift 467373
  have htrace : WordTrace (prefixWord ++ tailWord_467373) baseStart_467373 baseEnd_467373 := by
    simpa [prefixWord, tailWord_467373, baseEnd_467373] using wordTrace_append hprefix tailTrace_467373
  have hstable : (prefixWord ++ tailWord_467373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467373).length < 2 ^ (prefixWord ++ tailWord_467373).sum := by decide
  have hdescent : baseEnd_467373 < baseStart_467373 := by decide
  rcases family_descends (prefixWord ++ tailWord_467373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467463 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_467463 : Nat := 118140960795 + 467463 * 2 ^ 59
def prefixEnd_467463 : Nat := 4983230072969 + 3 ^ 40 * 467463 * 2
def baseEnd_467463 : Nat := 106681425419026570027859

theorem tailTrace_467463 : CollatzResearch.WordTrace tailWord_467463 prefixEnd_467463 106681425419026570027859 := by
  unfold tailWord_467463
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049776305468862169415043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11366517536979241446276695 17049776305468862169415043)
  ·
    refine ⟨25574664458203293254122565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17049776305468862169415043 25574664458203293254122565)
    ·
      refine ⟨4795249585913117485147981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25574664458203293254122565 4795249585913117485147981)
      ·
        refine ⟨1798218594717419056930493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4795249585913117485147981 1798218594717419056930493)
        ·
          refine ⟨674331973019032146348935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1798218594717419056930493 674331973019032146348935)
          ·
            refine ⟨1011497959528548219523403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674331973019032146348935 1011497959528548219523403)
            ·
              refine ⟨1517246939292822329285105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011497959528548219523403 1517246939292822329285105)
              ·
                refine ⟨1137935204469616746963829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517246939292822329285105 1137935204469616746963829)
                ·
                  refine ⟨106681425419026570027859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1137935204469616746963829 106681425419026570027859)
                  ·
                    rfl

theorem cell21_467463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_467463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467463 prefixEnd_467463 := by exact prefixLift 467463
  have htrace : WordTrace (prefixWord ++ tailWord_467463) baseStart_467463 baseEnd_467463 := by
    simpa [prefixWord, tailWord_467463, baseEnd_467463] using wordTrace_append hprefix tailTrace_467463
  have hstable : (prefixWord ++ tailWord_467463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467463).length < 2 ^ (prefixWord ++ tailWord_467463).sum := by decide
  have hdescent : baseEnd_467463 < baseStart_467463 := by decide
  rcases family_descends (prefixWord ++ tailWord_467463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467480 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_467480 : Nat := 118140960795 + 467480 * 2 ^ 59
def prefixEnd_467480 : Nat := 4983230072969 + 3 ^ 40 * 467480 * 2
def baseEnd_467480 : Nat := 106685305050638318244491

theorem tailTrace_467480 : CollatzResearch.WordTrace tailWord_467480 prefixEnd_467480 106685305050638318244491 := by
  unfold tailWord_467480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525198173203637036391947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11366930897604849381855929 8525198173203637036391947)
  ·
    refine ⟨12787797259805455554587921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8525198173203637036391947 12787797259805455554587921)
    ·
      refine ⟨9590847944854091665940941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12787797259805455554587921 9590847944854091665940941)
      ·
        refine ⟨3596567979320284374727853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9590847944854091665940941 3596567979320284374727853)
        ·
          refine ⟨1348712992245106640522945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3596567979320284374727853 1348712992245106640522945)
          ·
            refine ⟨1011534744183829980392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348712992245106640522945 1011534744183829980392209)
            ·
              refine ⟨758651058137872485294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011534744183829980392209 758651058137872485294157)
              ·
                refine ⟨284494146801702181985309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758651058137872485294157 284494146801702181985309)
                ·
                  refine ⟨106685305050638318244491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284494146801702181985309 106685305050638318244491)
                  ·
                    rfl

theorem cell21_467480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_467480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467480 prefixEnd_467480 := by exact prefixLift 467480
  have htrace : WordTrace (prefixWord ++ tailWord_467480) baseStart_467480 baseEnd_467480 := by
    simpa [prefixWord, tailWord_467480, baseEnd_467480] using wordTrace_append hprefix tailTrace_467480
  have hstable : (prefixWord ++ tailWord_467480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467480).length < 2 ^ (prefixWord ++ tailWord_467480).sum := by decide
  have hdescent : baseEnd_467480 < baseStart_467480 := by decide
  rcases family_descends (prefixWord ++ tailWord_467480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467491 : List Nat := [1, 1, 1, 4, 4, 2, 8]
def baseStart_467491 : Nat := 118140960795 + 467491 * 2 ^ 59
def prefixEnd_467491 : Nat := 4983230072969 + 3 ^ 40 * 467491 * 2
def baseEnd_467491 : Nat := 11854201711167193729015

theorem tailTrace_467491 : CollatzResearch.WordTrace tailWord_467491 prefixEnd_467491 11854201711167193729015 := by
  unfold tailWord_467491
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050797549367422951434327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11367198366244948634289551 17050797549367422951434327)
  ·
    refine ⟨25576196324051134427151491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17050797549367422951434327 25576196324051134427151491)
    ·
      refine ⟨38364294486076701640727237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25576196324051134427151491 38364294486076701640727237)
      ·
        refine ⟨7193305216139381557636357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38364294486076701640727237 7193305216139381557636357)
        ·
          refine ⟨1348744728026134042056817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7193305216139381557636357 1348744728026134042056817)
          ·
            refine ⟨1011558546019600531542613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348744728026134042056817 1011558546019600531542613)
            ·
              refine ⟨11854201711167193729015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1011558546019600531542613 11854201711167193729015)
              ·
                rfl

theorem cell21_467491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_467491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467491 prefixEnd_467491 := by exact prefixLift 467491
  have htrace : WordTrace (prefixWord ++ tailWord_467491) baseStart_467491 baseEnd_467491 := by
    simpa [prefixWord, tailWord_467491, baseEnd_467491] using wordTrace_append hprefix tailTrace_467491
  have hstable : (prefixWord ++ tailWord_467491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467491).length < 2 ^ (prefixWord ++ tailWord_467491).sum := by decide
  have hdescent : baseEnd_467491 < baseStart_467491 := by decide
  rcases family_descends (prefixWord ++ tailWord_467491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467556 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_467556 : Nat := 118140960795 + 467556 * 2 ^ 59
def prefixEnd_467556 : Nat := 4983230072969 + 3 ^ 40 * 467556 * 2
def baseEnd_467556 : Nat := 106702649286079074977669

theorem tailTrace_467556 : CollatzResearch.WordTrace tailWord_467556 prefixEnd_467556 106702649286079074977669 := by
  unfold tailWord_467556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526584147065969526275261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11368778862754626035033681 8526584147065969526275261)
  ·
    refine ⟨3197469055149738572353223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8526584147065969526275261 3197469055149738572353223)
    ·
      refine ⟨4796203582724607858529835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197469055149738572353223 4796203582724607858529835)
      ·
        refine ⟨7194305374086911787794753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796203582724607858529835 7194305374086911787794753)
        ·
          refine ⟨5395729030565183840846065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7194305374086911787794753 5395729030565183840846065)
          ·
            refine ⟨4046796772923887880634549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395729030565183840846065 4046796772923887880634549)
            ·
              refine ⟨379387197461614488809489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4046796772923887880634549 379387197461614488809489)
              ·
                refine ⟨284540398096210866607117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379387197461614488809489 284540398096210866607117)
                ·
                  refine ⟨106702649286079074977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284540398096210866607117 106702649286079074977669)
                  ·
                    rfl

theorem cell21_467556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_467556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467556 prefixEnd_467556 := by exact prefixLift 467556
  have htrace : WordTrace (prefixWord ++ tailWord_467556) baseStart_467556 baseEnd_467556 := by
    simpa [prefixWord, tailWord_467556, baseEnd_467556] using wordTrace_append hprefix tailTrace_467556
  have hstable : (prefixWord ++ tailWord_467556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467556).length < 2 ^ (prefixWord ++ tailWord_467556).sum := by decide
  have hdescent : baseEnd_467556 < baseStart_467556 := by decide
  rcases family_descends (prefixWord ++ tailWord_467556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467570 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_467570 : Nat := 118140960795 + 467570 * 2 ^ 59
def prefixEnd_467570 : Nat := 4983230072969 + 3 ^ 40 * 467570 * 2
def baseEnd_467570 : Nat := 106705844276818161744307

theorem tailTrace_467570 : CollatzResearch.WordTrace tailWord_467570 prefixEnd_467570 106705844276818161744307 := by
  unfold tailWord_467570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263419729020304860890041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11369119277387479629040109 4263419729020304860890041)
  ·
    refine ⟨3197564796765228645667531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4263419729020304860890041 3197564796765228645667531)
    ·
      refine ⟨4796347195147842968501297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197564796765228645667531 4796347195147842968501297)
      ·
        refine ⟨3597260396360882226375973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796347195147842968501297 3597260396360882226375973)
        ·
          refine ⟨674486324317665417445495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3597260396360882226375973 674486324317665417445495)
          ·
            refine ⟨1011729486476498126168243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674486324317665417445495 1011729486476498126168243)
            ·
              refine ⟨1517594229714747189252365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011729486476498126168243 1517594229714747189252365)
              ·
                refine ⟨569097836143030195969637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517594229714747189252365 569097836143030195969637)
                ·
                  refine ⟨106705844276818161744307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569097836143030195969637 106705844276818161744307)
                  ·
                    rfl

theorem cell21_467570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_467570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467570 prefixEnd_467570 := by exact prefixLift 467570
  have htrace : WordTrace (prefixWord ++ tailWord_467570) baseStart_467570 baseEnd_467570 := by
    simpa [prefixWord, tailWord_467570, baseEnd_467570] using wordTrace_append hprefix tailTrace_467570
  have hstable : (prefixWord ++ tailWord_467570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467570).length < 2 ^ (prefixWord ++ tailWord_467570).sum := by decide
  have hdescent : baseEnd_467570 < baseStart_467570 := by decide
  rcases family_descends (prefixWord ++ tailWord_467570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467674 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_467674 : Nat := 118140960795 + 467674 * 2 ^ 59
def prefixEnd_467674 : Nat := 4983230072969 + 3 ^ 40 * 467674 * 2
def baseEnd_467674 : Nat := 106729578493737092010761

theorem tailTrace_467674 : CollatzResearch.WordTrace tailWord_467674 prefixEnd_467674 106729578493737092010761 := by
  unfold tailWord_467674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264368026926111301336519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11371648071802963470230717 4264368026926111301336519)
  ·
    refine ⟨6396552040389166952004779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4264368026926111301336519 6396552040389166952004779)
    ·
      refine ⟨9594828060583750428007169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396552040389166952004779 9594828060583750428007169)
      ·
        refine ⟨7196121045437812821005377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9594828060583750428007169 7196121045437812821005377)
        ·
          refine ⟨5397090784078359615754033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7196121045437812821005377 5397090784078359615754033)
          ·
            refine ⟨4047818088058769711815525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397090784078359615754033 4047818088058769711815525)
            ·
              refine ⟨758965891511019320965411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4047818088058769711815525 758965891511019320965411)
              ·
                refine ⟨1138448837266528981448117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758965891511019320965411 1138448837266528981448117)
                ·
                  refine ⟨106729578493737092010761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138448837266528981448117 106729578493737092010761)
                  ·
                    rfl

theorem cell21_467674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_467674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467674 prefixEnd_467674 := by exact prefixLift 467674
  have htrace : WordTrace (prefixWord ++ tailWord_467674) baseStart_467674 baseEnd_467674 := by
    simpa [prefixWord, tailWord_467674, baseEnd_467674] using wordTrace_append hprefix tailTrace_467674
  have hstable : (prefixWord ++ tailWord_467674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467674).length < 2 ^ (prefixWord ++ tailWord_467674).sum := by decide
  have hdescent : baseEnd_467674 < baseStart_467674 := by decide
  rcases family_descends (prefixWord ++ tailWord_467674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467708 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_467708 : Nat := 118140960795 + 467708 * 2 ^ 59
def prefixEnd_467708 : Nat := 4983230072969 + 3 ^ 40 * 467708 * 2
def baseEnd_467708 : Nat := 106737337756960588444025

theorem tailTrace_467708 : CollatzResearch.WordTrace tailWord_467708 prefixEnd_467708 106737337756960588444025 := by
  unfold tailWord_467708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529356094790634506041889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11372474793054179341389185 8529356094790634506041889)
  ·
    refine ⟨6397017071092975879531417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8529356094790634506041889 6397017071092975879531417)
    ·
      refine ⟨4797762803319731909648563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6397017071092975879531417 4797762803319731909648563)
      ·
        refine ⟨7196644204979597864472845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797762803319731909648563 7196644204979597864472845)
        ·
          refine ⟨2698741576867349199177317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7196644204979597864472845 2698741576867349199177317)
          ·
            refine ⟨506014045662627974845747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2698741576867349199177317 506014045662627974845747)
            ·
              refine ⟨759021068493941962268621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506014045662627974845747 759021068493941962268621)
              ·
                refine ⟨284632900685228235850733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759021068493941962268621 284632900685228235850733)
                ·
                  refine ⟨106737337756960588444025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284632900685228235850733 106737337756960588444025)
                  ·
                    rfl

theorem cell21_467708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_467708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467708 prefixEnd_467708 := by exact prefixLift 467708
  have htrace : WordTrace (prefixWord ++ tailWord_467708) baseStart_467708 baseEnd_467708 := by
    simpa [prefixWord, tailWord_467708, baseEnd_467708] using wordTrace_append hprefix tailTrace_467708
  have hstable : (prefixWord ++ tailWord_467708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467708).length < 2 ^ (prefixWord ++ tailWord_467708).sum := by decide
  have hdescent : baseEnd_467708 < baseStart_467708 := by decide
  rcases family_descends (prefixWord ++ tailWord_467708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467719 : List Nat := [1, 1, 4, 4, 1, 1, 9]
def baseStart_467719 : Nat := 118140960795 + 467719 * 2 ^ 59
def prefixEnd_467719 : Nat := 4983230072969 + 3 ^ 40 * 467719 * 2
def baseEnd_467719 : Nat := 11859983122980779306741

theorem tailTrace_467719 : CollatzResearch.WordTrace tailWord_467719 prefixEnd_467719 11859983122980779306741 := by
  unfold tailWord_467719
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059113392541417890734211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11372742261694278593822807 17059113392541417890734211)
  ·
    refine ⟨25588670088812126836101317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059113392541417890734211 25588670088812126836101317)
    ·
      refine ⟨4797875641652273781768997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25588670088812126836101317 4797875641652273781768997)
      ·
        refine ⟨899601682809801334081687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4797875641652273781768997 899601682809801334081687)
        ·
          refine ⟨1349402524214702001122531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899601682809801334081687 1349402524214702001122531)
          ·
            refine ⟨2024103786322053001683797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349402524214702001122531 2024103786322053001683797)
            ·
              refine ⟨11859983122980779306741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2024103786322053001683797 11859983122980779306741)
              ·
                rfl

theorem cell21_467719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_467719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467719 prefixEnd_467719 := by exact prefixLift 467719
  have htrace : WordTrace (prefixWord ++ tailWord_467719) baseStart_467719 baseEnd_467719 := by
    simpa [prefixWord, tailWord_467719, baseEnd_467719] using wordTrace_append hprefix tailTrace_467719
  have hstable : (prefixWord ++ tailWord_467719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467719).length < 2 ^ (prefixWord ++ tailWord_467719).sum := by decide
  have hdescent : baseEnd_467719 < baseStart_467719 := by decide
  rcases family_descends (prefixWord ++ tailWord_467719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467812 : List Nat := [2, 3, 1, 1, 4, 2, 3, 5]
def baseStart_467812 : Nat := 118140960795 + 467812 * 2 ^ 59
def prefixEnd_467812 : Nat := 4983230072969 + 3 ^ 40 * 467812 * 2
def baseEnd_467812 : Nat := 35587023991293172903493

theorem tailTrace_467812 : CollatzResearch.WordTrace tailWord_467812 prefixEnd_467812 35587023991293172903493 := by
  unfold tailWord_467812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531252690602247386934845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11375003587469663182579793 8531252690602247386934845)
  ·
    refine ⟨3199219758975842770100567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8531252690602247386934845 3199219758975842770100567)
    ·
      refine ⟨4798829638463764155150851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199219758975842770100567 4798829638463764155150851)
      ·
        refine ⟨7198244457695646232726277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798829638463764155150851 7198244457695646232726277)
        ·
          refine ⟨1349670835817933668636177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7198244457695646232726277 1349670835817933668636177)
          ·
            refine ⟨1012253126863450251477133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349670835817933668636177 1012253126863450251477133)
            ·
              refine ⟨379594922573793844303925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012253126863450251477133 379594922573793844303925)
              ·
                refine ⟨35587023991293172903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379594922573793844303925 35587023991293172903493)
                ·
                  rfl

theorem cell21_467812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_467812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467812 prefixEnd_467812 := by exact prefixLift 467812
  have htrace : WordTrace (prefixWord ++ tailWord_467812) baseStart_467812 baseEnd_467812 := by
    simpa [prefixWord, tailWord_467812, baseEnd_467812] using wordTrace_append hprefix tailTrace_467812
  have hstable : (prefixWord ++ tailWord_467812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467812).length < 2 ^ (prefixWord ++ tailWord_467812).sum := by decide
  have hdescent : baseEnd_467812 < baseStart_467812 := by decide
  rcases family_descends (prefixWord ++ tailWord_467812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467840 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_467840 : Nat := 118140960795 + 467840 * 2 ^ 59
def prefixEnd_467840 : Nat := 4983230072969 + 3 ^ 40 * 467840 * 2
def baseEnd_467840 : Nat := 106767461955357692243755

theorem tailTrace_467840 : CollatzResearch.WordTrace tailWord_467840 prefixEnd_467840 106767461955357692243755 := by
  unfold tailWord_467840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531763312551527777944487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11375684416735370370592649 8531763312551527777944487)
  ·
    refine ⟨12797644968827291666916731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8531763312551527777944487 12797644968827291666916731)
    ·
      refine ⟨19196467453240937500375097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12797644968827291666916731 19196467453240937500375097)
      ·
        refine ⟨14397350589930703125281323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19196467453240937500375097 14397350589930703125281323)
        ·
          refine ⟨21596025884896054687921985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397350589930703125281323 21596025884896054687921985)
          ·
            refine ⟨16197019413672041015941489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21596025884896054687921985 16197019413672041015941489)
            ·
              refine ⟨12147764560254030761956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16197019413672041015941489 12147764560254030761956117)
              ·
                refine ⟨569426463761907691966693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12147764560254030761956117 569426463761907691966693)
                ·
                  refine ⟨106767461955357692243755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569426463761907691966693 106767461955357692243755)
                  ·
                    rfl

theorem cell21_467840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_467840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467840 prefixEnd_467840 := by exact prefixLift 467840
  have htrace : WordTrace (prefixWord ++ tailWord_467840) baseStart_467840 baseEnd_467840 := by
    simpa [prefixWord, tailWord_467840, baseEnd_467840] using wordTrace_append hprefix tailTrace_467840
  have hstable : (prefixWord ++ tailWord_467840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467840).length < 2 ^ (prefixWord ++ tailWord_467840).sum := by decide
  have hdescent : baseEnd_467840 < baseStart_467840 := by decide
  rcases family_descends (prefixWord ++ tailWord_467840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467871 : List Nat := [1, 1, 2, 5, 2, 2, 1, 7]
def baseStart_467871 : Nat := 118140960795 + 467871 * 2 ^ 59
def prefixEnd_467871 : Nat := 4983230072969 + 3 ^ 40 * 467871 * 2
def baseEnd_467871 : Nat := 35591512192569509075675

theorem tailTrace_467871 : CollatzResearch.WordTrace tailWord_467871 prefixEnd_467871 35591512192569509075675 := by
  unfold tailWord_467871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064657287990747850267467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11376438191993831900178311 17064657287990747850267467)
  ·
    refine ⟨25596985931986121775401201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17064657287990747850267467 25596985931986121775401201)
    ·
      refine ⟨19197739448989591331550901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25596985931986121775401201 19197739448989591331550901)
      ·
        refine ⟨1799788073342774187332897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19197739448989591331550901 1799788073342774187332897)
        ·
          refine ⟨1349841055007080640499673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799788073342774187332897 1349841055007080640499673)
          ·
            refine ⟨1012380791255310480374755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349841055007080640499673 1012380791255310480374755)
            ·
              refine ⟨1518571186882965720562133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012380791255310480374755 1518571186882965720562133)
              ·
                refine ⟨35591512192569509075675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1518571186882965720562133 35591512192569509075675)
                ·
                  rfl

theorem cell21_467871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_467871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467871 prefixEnd_467871 := by exact prefixLift 467871
  have htrace : WordTrace (prefixWord ++ tailWord_467871) baseStart_467871 baseEnd_467871 := by
    simpa [prefixWord, tailWord_467871, baseEnd_467871] using wordTrace_append hprefix tailTrace_467871
  have hstable : (prefixWord ++ tailWord_467871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467871).length < 2 ^ (prefixWord ++ tailWord_467871).sum := by decide
  have hdescent : baseEnd_467871 < baseStart_467871 := by decide
  rcases family_descends (prefixWord ++ tailWord_467871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467894 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_467894 : Nat := 118140960795 + 467894 * 2 ^ 59
def prefixEnd_467894 : Nat := 4983230072969 + 3 ^ 40 * 467894 * 2
def baseEnd_467894 : Nat := 106779785491065598343645

theorem tailTrace_467894 : CollatzResearch.WordTrace tailWord_467894 prefixEnd_467894 106779785491065598343645 := by
  unfold tailWord_467894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066593510431713923647171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11376997444604948518903157 1066593510431713923647171)
  ·
    refine ⟨1599890265647570885470757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1066593510431713923647171 1599890265647570885470757)
    ·
      refine ⟨299979424808919541025767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1599890265647570885470757 299979424808919541025767)
      ·
        refine ⟨449969137213379311538651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299979424808919541025767 449969137213379311538651)
        ·
          refine ⟨674953705820068967307977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449969137213379311538651 674953705820068967307977)
          ·
            refine ⟨506215279365051725480983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674953705820068967307977 506215279365051725480983)
            ·
              refine ⟨759322919047577588221475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506215279365051725480983 759322919047577588221475)
              ·
                refine ⟨1138984378571366382332213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759322919047577588221475 1138984378571366382332213)
                ·
                  refine ⟨106779785491065598343645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138984378571366382332213 106779785491065598343645)
                  ·
                    rfl

theorem cell21_467894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_467894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467894 prefixEnd_467894 := by exact prefixLift 467894
  have htrace : WordTrace (prefixWord ++ tailWord_467894) baseStart_467894 baseEnd_467894 := by
    simpa [prefixWord, tailWord_467894, baseEnd_467894] using wordTrace_append hprefix tailTrace_467894
  have hstable : (prefixWord ++ tailWord_467894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467894).length < 2 ^ (prefixWord ++ tailWord_467894).sum := by decide
  have hdescent : baseEnd_467894 < baseStart_467894 := by decide
  rcases family_descends (prefixWord ++ tailWord_467894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467899 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_467899 : Nat := 118140960795 + 467899 * 2 ^ 59
def prefixEnd_467899 : Nat := 4983230072969 + 3 ^ 40 * 467899 * 2
def baseEnd_467899 : Nat := 106780926559186700760301

theorem tailTrace_467899 : CollatzResearch.WordTrace tailWord_467899 prefixEnd_467899 106780926559186700760301 := by
  unfold tailWord_467899
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065678531889308632286751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11377119021259539088191167 17065678531889308632286751)
  ·
    refine ⟨25598517797833962948430127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17065678531889308632286751 25598517797833962948430127)
    ·
      refine ⟨38397776696750944422645191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25598517797833962948430127 38397776696750944422645191)
      ·
        refine ⟨57596665045126416633967787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38397776696750944422645191 57596665045126416633967787)
        ·
          refine ⟨86394997567689624950951681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57596665045126416633967787 86394997567689624950951681)
          ·
            refine ⟨64796248175767218713213761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86394997567689624950951681 64796248175767218713213761)
            ·
              refine ⟨48597186131825414034910321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64796248175767218713213761 48597186131825414034910321)
              ·
                refine ⟨36447889598869060526182741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48597186131825414034910321 36447889598869060526182741)
                ·
                  refine ⟨106780926559186700760301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 36447889598869060526182741 106780926559186700760301)
                  ·
                    rfl

theorem cell21_467899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_467899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467899 prefixEnd_467899 := by exact prefixLift 467899
  have htrace : WordTrace (prefixWord ++ tailWord_467899) baseStart_467899 baseEnd_467899 := by
    simpa [prefixWord, tailWord_467899, baseEnd_467899] using wordTrace_append hprefix tailTrace_467899
  have hstable : (prefixWord ++ tailWord_467899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467899).length < 2 ^ (prefixWord ++ tailWord_467899).sum := by decide
  have hdescent : baseEnd_467899 < baseStart_467899 := by decide
  rcases family_descends (prefixWord ++ tailWord_467899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467908 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_467908 : Nat := 118140960795 + 467908 * 2 ^ 59
def prefixEnd_467908 : Nat := 4983230072969 + 3 ^ 40 * 467908 * 2
def baseEnd_467908 : Nat := 106782980481804685110283

theorem tailTrace_467908 : CollatzResearch.WordTrace tailWord_467908 prefixEnd_467908 106782980481804685110283 := by
  unfold tailWord_467908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533003394428351584682189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11377337859237802112909585 8533003394428351584682189)
  ·
    refine ⟨3199876272910631844255821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8533003394428351584682189 3199876272910631844255821)
    ·
      refine ⟨1199953602341486941595933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3199876272910631844255821 1199953602341486941595933)
      ·
        refine ⟨449982600878057603098475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1199953602341486941595933 449982600878057603098475)
        ·
          refine ⟨674973901317086404647713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449982600878057603098475 674973901317086404647713)
          ·
            refine ⟨506230425987814803485785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674973901317086404647713 506230425987814803485785)
            ·
              refine ⟨379672819490861102614339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506230425987814803485785 379672819490861102614339)
              ·
                refine ⟨569509229236291653921509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379672819490861102614339 569509229236291653921509)
                ·
                  refine ⟨106782980481804685110283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569509229236291653921509 106782980481804685110283)
                  ·
                    rfl

theorem cell21_467908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_467908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467908 prefixEnd_467908 := by exact prefixLift 467908
  have htrace : WordTrace (prefixWord ++ tailWord_467908) baseStart_467908 baseEnd_467908 := by
    simpa [prefixWord, tailWord_467908, baseEnd_467908] using wordTrace_append hprefix tailTrace_467908
  have hstable : (prefixWord ++ tailWord_467908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467908).length < 2 ^ (prefixWord ++ tailWord_467908).sum := by decide
  have hdescent : baseEnd_467908 < baseStart_467908 := by decide
  rcases family_descends (prefixWord ++ tailWord_467908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467950 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_467950 : Nat := 118140960795 + 467950 * 2 ^ 59
def prefixEnd_467950 : Nat := 4983230072969 + 3 ^ 40 * 467950 * 2
def baseEnd_467950 : Nat := 106792565454021945410197

theorem tailTrace_467950 : CollatzResearch.WordTrace tailWord_467950 prefixEnd_467950 106792565454021945410197 := by
  unfold tailWord_467950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133442331838068042799163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11378359103136362894928869 2133442331838068042799163)
  ·
    refine ⟨3200163497757102064198745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133442331838068042799163 3200163497757102064198745)
    ·
      refine ⟨2400122623317826548149059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3200163497757102064198745 2400122623317826548149059)
      ·
        refine ⟨3600183934976739822223589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400122623317826548149059 3600183934976739822223589)
        ·
          refine ⟨675034487808138716666923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3600183934976739822223589 675034487808138716666923)
          ·
            refine ⟨1012551731712208075000385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675034487808138716666923 1012551731712208075000385)
            ·
              refine ⟨759413798784156056250289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012551731712208075000385 759413798784156056250289)
              ·
                refine ⟨569560349088117042187717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759413798784156056250289 569560349088117042187717)
                ·
                  refine ⟨106792565454021945410197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569560349088117042187717 106792565454021945410197)
                  ·
                    rfl

theorem cell21_467950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_467950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467950 prefixEnd_467950 := by exact prefixLift 467950
  have htrace : WordTrace (prefixWord ++ tailWord_467950) baseStart_467950 baseEnd_467950 := by
    simpa [prefixWord, tailWord_467950, baseEnd_467950] using wordTrace_append hprefix tailTrace_467950
  have hstable : (prefixWord ++ tailWord_467950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467950).length < 2 ^ (prefixWord ++ tailWord_467950).sum := by decide
  have hdescent : baseEnd_467950 < baseStart_467950 := by decide
  rcases family_descends (prefixWord ++ tailWord_467950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467956 : List Nat := [2, 6, 2, 1, 2, 1, 1, 6]
def baseStart_467956 : Nat := 118140960795 + 467956 * 2 ^ 59
def prefixEnd_467956 : Nat := 4983230072969 + 3 ^ 40 * 467956 * 2
def baseEnd_467956 : Nat := 35597978245255756103395

theorem tailTrace_467956 : CollatzResearch.WordTrace tailWord_467956 prefixEnd_467956 35597978245255756103395 := by
  unfold tailWord_467956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533878746341403683555861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11378504995121871578074481 8533878746341403683555861)
  ·
    refine ⟨400025566234753297666681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8533878746341403683555861 400025566234753297666681)
    ·
      refine ⟨300019174676064973250011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400025566234753297666681 300019174676064973250011)
      ·
        refine ⟨450028762014097459875017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300019174676064973250011 450028762014097459875017)
        ·
          refine ⟨337521571510573094906263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450028762014097459875017 337521571510573094906263)
          ·
            refine ⟨506282357265859642359395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337521571510573094906263 506282357265859642359395)
            ·
              refine ⟨759423535898789463539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506282357265859642359395 759423535898789463539093)
              ·
                refine ⟨35597978245255756103395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 759423535898789463539093 35597978245255756103395)
                ·
                  rfl

theorem cell21_467956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_467956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467956 prefixEnd_467956 := by exact prefixLift 467956
  have htrace : WordTrace (prefixWord ++ tailWord_467956) baseStart_467956 baseEnd_467956 := by
    simpa [prefixWord, tailWord_467956, baseEnd_467956] using wordTrace_append hprefix tailTrace_467956
  have hstable : (prefixWord ++ tailWord_467956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467956).length < 2 ^ (prefixWord ++ tailWord_467956).sum := by decide
  have hdescent : baseEnd_467956 < baseStart_467956 := by decide
  rcases family_descends (prefixWord ++ tailWord_467956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467961 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_467961 : Nat := 118140960795 + 467961 * 2 ^ 59
def prefixEnd_467961 : Nat := 4983230072969 + 3 ^ 40 * 467961 * 2
def baseEnd_467961 : Nat := 106795075803888370726841

theorem tailTrace_467961 : CollatzResearch.WordTrace tailWord_467961 prefixEnd_467961 106795075803888370726841 := by
  unfold tailWord_467961
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067939857664693221043737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11378626571776462147362491 17067939857664693221043737)
  ·
    refine ⟨12800954893248519915782803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17067939857664693221043737 12800954893248519915782803)
    ·
      refine ⟨19201432339872779873674205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12800954893248519915782803 19201432339872779873674205)
      ·
        refine ⟨7200537127452292452627827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19201432339872779873674205 7200537127452292452627827)
        ·
          refine ⟨10800805691178438678941741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200537127452292452627827 10800805691178438678941741)
          ·
            refine ⟨4050302134191914504603153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10800805691178438678941741 4050302134191914504603153)
            ·
              refine ⟨3037726600643935878452365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050302134191914504603153 3037726600643935878452365)
              ·
                refine ⟨1139147475241475954419637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3037726600643935878452365 1139147475241475954419637)
                ·
                  refine ⟨106795075803888370726841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139147475241475954419637 106795075803888370726841)
                  ·
                    rfl

theorem cell21_467961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_467961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467961 prefixEnd_467961 := by exact prefixLift 467961
  have htrace : WordTrace (prefixWord ++ tailWord_467961) baseStart_467961 baseEnd_467961 := by
    simpa [prefixWord, tailWord_467961, baseEnd_467961] using wordTrace_append hprefix tailTrace_467961
  have hstable : (prefixWord ++ tailWord_467961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467961).length < 2 ^ (prefixWord ++ tailWord_467961).sum := by decide
  have hdescent : baseEnd_467961 < baseStart_467961 := by decide
  rcases family_descends (prefixWord ++ tailWord_467961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467978 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_467978 : Nat := 118140960795 + 467978 * 2 ^ 59
def prefixEnd_467978 : Nat := 4983230072969 + 3 ^ 40 * 467978 * 2
def baseEnd_467978 : Nat := 106798955435500118943473

theorem tailTrace_467978 : CollatzResearch.WordTrace tailWord_467978 prefixEnd_467978 106798955435500118943473 := by
  unfold tailWord_467978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267139974650776281103147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11379039932402070082941725 4267139974650776281103147)
  ·
    refine ⟨6400709961976164421654721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4267139974650776281103147 6400709961976164421654721)
    ·
      refine ⟨4800532471482123316241041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6400709961976164421654721 4800532471482123316241041)
      ·
        refine ⟨3600399353611592487180781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4800532471482123316241041 3600399353611592487180781)
        ·
          refine ⟨1350149757604347182692793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3600399353611592487180781 1350149757604347182692793)
          ·
            refine ⟨1012612318203260387019595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350149757604347182692793 1012612318203260387019595)
            ·
              refine ⟨1518918477304890580529393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012612318203260387019595 1518918477304890580529393)
              ·
                refine ⟨1139188857978667935397045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518918477304890580529393 1139188857978667935397045)
                ·
                  refine ⟨106798955435500118943473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139188857978667935397045 106798955435500118943473)
                  ·
                    rfl

theorem cell21_467978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_467978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_467978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_467978 prefixEnd_467978 := by exact prefixLift 467978
  have htrace : WordTrace (prefixWord ++ tailWord_467978) baseStart_467978 baseEnd_467978 := by
    simpa [prefixWord, tailWord_467978, baseEnd_467978] using wordTrace_append hprefix tailTrace_467978
  have hstable : (prefixWord ++ tailWord_467978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467978).length < 2 ^ (prefixWord ++ tailWord_467978).sum := by decide
  have hdescent : baseEnd_467978 < baseStart_467978 := by decide
  rcases family_descends (prefixWord ++ tailWord_467978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468037 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_468037 : Nat := 118140960795 + 468037 * 2 ^ 59
def prefixEnd_468037 : Nat := 4983230072969 + 3 ^ 40 * 468037 * 2
def baseEnd_468037 : Nat := 106812420039329127460019

theorem tailTrace_468037 : CollatzResearch.WordTrace tailWord_468037 prefixEnd_468037 106812420039329127460019 := by
  unfold tailWord_468037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070711805389358200810365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11380474536926238800540243 17070711805389358200810365)
  ·
    refine ⟨6401516927021009325303887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17070711805389358200810365 6401516927021009325303887)
    ·
      refine ⟨9602275390531513987955831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401516927021009325303887 9602275390531513987955831)
      ·
        refine ⟨14403413085797270981933747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602275390531513987955831 14403413085797270981933747)
        ·
          refine ⟨21605119628695906472900621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403413085797270981933747 21605119628695906472900621)
          ·
            refine ⟨8101919860760964927337733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21605119628695906472900621 8101919860760964927337733)
            ·
              refine ⟨1519109973892680923875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8101919860760964927337733 1519109973892680923875825)
              ·
                refine ⟨1139332480419510692906869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519109973892680923875825 1139332480419510692906869)
                ·
                  refine ⟨106812420039329127460019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139332480419510692906869 106812420039329127460019)
                  ·
                    rfl

theorem cell21_468037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_468037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468037 prefixEnd_468037 := by exact prefixLift 468037
  have htrace : WordTrace (prefixWord ++ tailWord_468037) baseStart_468037 baseEnd_468037 := by
    simpa [prefixWord, tailWord_468037, baseEnd_468037] using wordTrace_append hprefix tailTrace_468037
  have hstable : (prefixWord ++ tailWord_468037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468037).length < 2 ^ (prefixWord ++ tailWord_468037).sum := by decide
  have hdescent : baseEnd_468037 < baseStart_468037 := by decide
  rcases family_descends (prefixWord ++ tailWord_468037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468051 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_468051 : Nat := 118140960795 + 468051 * 2 ^ 59
def prefixEnd_468051 : Nat := 4983230072969 + 3 ^ 40 * 468051 * 2
def baseEnd_468051 : Nat := 106815615030068214226657

theorem tailTrace_468051 : CollatzResearch.WordTrace tailWord_468051 prefixEnd_468051 106815615030068214226657 := by
  unfold tailWord_468051
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071222427338638591820007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11380814951559092394546671 17071222427338638591820007)
  ·
    refine ⟨25606833641007957887730011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17071222427338638591820007 25606833641007957887730011)
    ·
      refine ⟨38410250461511936831595017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25606833641007957887730011 38410250461511936831595017)
      ·
        refine ⟨28807687846133952623696263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38410250461511936831595017 28807687846133952623696263)
        ·
          refine ⟨43211531769200928935544395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28807687846133952623696263 43211531769200928935544395)
          ·
            refine ⟨64817297653801393403316593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43211531769200928935544395 64817297653801393403316593)
            ·
              refine ⟨48612973240351045052487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64817297653801393403316593 48612973240351045052487445)
              ·
                refine ⟨2278733120641455236835349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48612973240351045052487445 2278733120641455236835349)
                ·
                  refine ⟨106815615030068214226657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2278733120641455236835349 106815615030068214226657)
                  ·
                    rfl

theorem cell21_468051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_468051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468051 prefixEnd_468051 := by exact prefixLift 468051
  have htrace : WordTrace (prefixWord ++ tailWord_468051) baseStart_468051 baseEnd_468051 := by
    simpa [prefixWord, tailWord_468051, baseEnd_468051] using wordTrace_append hprefix tailTrace_468051
  have hstable : (prefixWord ++ tailWord_468051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468051).length < 2 ^ (prefixWord ++ tailWord_468051).sum := by decide
  have hdescent : baseEnd_468051 < baseStart_468051 := by decide
  rcases family_descends (prefixWord ++ tailWord_468051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468068 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_468068 : Nat := 118140960795 + 468068 * 2 ^ 59
def prefixEnd_468068 : Nat := 4983230072969 + 3 ^ 40 * 468068 * 2
def baseEnd_468068 : Nat := 106819494661679962443289

theorem tailTrace_468068 : CollatzResearch.WordTrace tailWord_468068 prefixEnd_468068 106819494661679962443289 := by
  unfold tailWord_468068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535921234138525247594429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11381228312184700330125905 8535921234138525247594429)
  ·
    refine ⟨3200970462801946967847911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8535921234138525247594429 3200970462801946967847911)
    ·
      refine ⟨4801455694202920451771867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200970462801946967847911 4801455694202920451771867)
      ·
        refine ⟨7202183541304380677657801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801455694202920451771867 7202183541304380677657801)
        ·
          refine ⟨5401637655978285508243351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7202183541304380677657801 5401637655978285508243351)
          ·
            refine ⟨8102456483967428262365027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401637655978285508243351 8102456483967428262365027)
            ·
              refine ⟨12153684725951142393547541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102456483967428262365027 12153684725951142393547541)
              ·
                refine ⟨569703971528959799697541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12153684725951142393547541 569703971528959799697541)
                ·
                  refine ⟨106819494661679962443289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569703971528959799697541 106819494661679962443289)
                  ·
                    rfl

theorem cell21_468068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_468068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468068 prefixEnd_468068 := by exact prefixLift 468068
  have htrace : WordTrace (prefixWord ++ tailWord_468068) baseStart_468068 baseEnd_468068 := by
    simpa [prefixWord, tailWord_468068, baseEnd_468068] using wordTrace_append hprefix tailTrace_468068
  have hstable : (prefixWord ++ tailWord_468068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468068).length < 2 ^ (prefixWord ++ tailWord_468068).sum := by decide
  have hdescent : baseEnd_468068 < baseStart_468068 := by decide
  rcases family_descends (prefixWord ++ tailWord_468068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468150 : List Nat := [5, 1, 3, 2, 1, 1, 3, 5]
def baseStart_468150 : Nat := 118140960795 + 468150 * 2 ^ 59
def prefixEnd_468150 : Nat := 4983230072969 + 3 ^ 40 * 468150 * 2
def baseEnd_468150 : Nat := 35612736059622014025485

theorem tailTrace_468150 : CollatzResearch.WordTrace tailWord_468150 prefixEnd_468150 35612736059622014025485 := by
  unfold tailWord_468150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067177078373748656229619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11383222169319985666449269 1067177078373748656229619)
  ·
    refine ⟨1600765617560622984344429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067177078373748656229619 1600765617560622984344429)
    ·
      refine ⟨600287106585233619129161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1600765617560622984344429 600287106585233619129161)
      ·
        refine ⟨450215329938925214346871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600287106585233619129161 450215329938925214346871)
        ·
          refine ⟨675322994908387821520307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450215329938925214346871 675322994908387821520307)
          ·
            refine ⟨1012984492362581732280461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675322994908387821520307 1012984492362581732280461)
            ·
              refine ⟨379869184635968149605173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012984492362581732280461 379869184635968149605173)
              ·
                refine ⟨35612736059622014025485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379869184635968149605173 35612736059622014025485)
                ·
                  rfl

theorem cell21_468150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_468150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468150 prefixEnd_468150 := by exact prefixLift 468150
  have htrace : WordTrace (prefixWord ++ tailWord_468150) baseStart_468150 baseEnd_468150 := by
    simpa [prefixWord, tailWord_468150, baseEnd_468150] using wordTrace_append hprefix tailTrace_468150
  have hstable : (prefixWord ++ tailWord_468150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468150).length < 2 ^ (prefixWord ++ tailWord_468150).sum := by decide
  have hdescent : baseEnd_468150 < baseStart_468150 := by decide
  rcases family_descends (prefixWord ++ tailWord_468150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468164 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_468164 : Nat := 118140960795 + 468164 * 2 ^ 59
def prefixEnd_468164 : Nat := 4983230072969 + 3 ^ 40 * 468164 * 2
def baseEnd_468164 : Nat := 106841403169605128843093

theorem tailTrace_468164 : CollatzResearch.WordTrace tailWord_468164 prefixEnd_468164 106841403169605128843093 := by
  unfold tailWord_468164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537671937964629445341773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11383562583952839260455697 8537671937964629445341773)
  ·
    refine ⟨3201626976736736042003165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8537671937964629445341773 3201626976736736042003165)
    ·
      refine ⟨1200610116276276015751187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3201626976736736042003165 1200610116276276015751187)
      ·
        refine ⟨1800915174414414023626781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200610116276276015751187 1800915174414414023626781)
        ·
          refine ⟨675343190405405258860043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1800915174414414023626781 675343190405405258860043)
          ·
            refine ⟨1013014785608107888290065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675343190405405258860043 1013014785608107888290065)
            ·
              refine ⟨759761089206080916217549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013014785608107888290065 759761089206080916217549)
              ·
                refine ⟨284910408452280343581581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759761089206080916217549 284910408452280343581581)
                ·
                  refine ⟨106841403169605128843093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284910408452280343581581 106841403169605128843093)
                  ·
                    rfl

theorem cell21_468164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_468164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468164 prefixEnd_468164 := by exact prefixLift 468164
  have htrace : WordTrace (prefixWord ++ tailWord_468164) baseStart_468164 baseEnd_468164 := by
    simpa [prefixWord, tailWord_468164, baseEnd_468164] using wordTrace_append hprefix tailTrace_468164
  have hstable : (prefixWord ++ tailWord_468164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468164).length < 2 ^ (prefixWord ++ tailWord_468164).sum := by decide
  have hdescent : baseEnd_468164 < baseStart_468164 := by decide
  rcases family_descends (prefixWord ++ tailWord_468164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468223 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 3]
def baseStart_468223 : Nat := 118140960795 + 468223 * 2 ^ 59
def prefixEnd_468223 : Nat := 4983230072969 + 3 ^ 40 * 468223 * 2
def baseEnd_468223 : Nat := 106854867773434137359639

theorem tailTrace_468223 : CollatzResearch.WordTrace tailWord_468223 prefixEnd_468223 106854867773434137359639 := by
  unfold tailWord_468223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077495782715511967081323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11384997188477007978054215 17077495782715511967081323)
  ·
    refine ⟨25616243674073267950621985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17077495782715511967081323 25616243674073267950621985)
    ·
      refine ⟨19212182755554950962966489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25616243674073267950621985 19212182755554950962966489)
      ·
        refine ⟨14409137066666213222224867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19212182755554950962966489 14409137066666213222224867)
        ·
          refine ⟨21613705599999319833337301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409137066666213222224867 21613705599999319833337301)
          ·
            refine ⟨506571224999984058593843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21613705599999319833337301 506571224999984058593843)
            ·
              refine ⟨759856837499976087890765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506571224999984058593843 759856837499976087890765)
              ·
                refine ⟨284946314062491032959037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759856837499976087890765 284946314062491032959037)
                ·
                  refine ⟨106854867773434137359639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284946314062491032959037 106854867773434137359639)
                  ·
                    rfl

theorem cell21_468223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].length) (baseStart_468223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468223 prefixEnd_468223 := by exact prefixLift 468223
  have htrace : WordTrace (prefixWord ++ tailWord_468223) baseStart_468223 baseEnd_468223 := by
    simpa [prefixWord, tailWord_468223, baseEnd_468223] using wordTrace_append hprefix tailTrace_468223
  have hstable : (prefixWord ++ tailWord_468223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468223).length < 2 ^ (prefixWord ++ tailWord_468223).sum := by decide
  have hdescent : baseEnd_468223 < baseStart_468223 := by decide
  rcases family_descends (prefixWord ++ tailWord_468223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468282 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_468282 : Nat := 118140960795 + 468282 * 2 ^ 59
def prefixEnd_468282 : Nat := 4983230072969 + 3 ^ 40 * 468282 * 2
def baseEnd_468282 : Nat := 106868332377263145876185

theorem tailTrace_468282 : CollatzResearch.WordTrace tailWord_468282 prefixEnd_468282 106868332377263145876185 := by
  unfold tailWord_468282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269911922375441260869775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11386431793001176695652733 4269911922375441260869775)
  ·
    refine ⟨6404867883563161891304663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269911922375441260869775 6404867883563161891304663)
    ·
      refine ⟨9607301825344742836956995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6404867883563161891304663 9607301825344742836956995)
      ·
        refine ⟨14410952738017114255435493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9607301825344742836956995 14410952738017114255435493)
        ·
          refine ⟨2702053638378208922894155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14410952738017114255435493 2702053638378208922894155)
          ·
            refine ⟨4053080457567313384341233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702053638378208922894155 4053080457567313384341233)
            ·
              refine ⟨3039810343175485038255925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053080457567313384341233 3039810343175485038255925)
              ·
                refine ⟨284982219672701722336493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3039810343175485038255925 284982219672701722336493)
                ·
                  refine ⟨106868332377263145876185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284982219672701722336493 106868332377263145876185)
                  ·
                    rfl

theorem cell21_468282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_468282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468282 prefixEnd_468282 := by exact prefixLift 468282
  have htrace : WordTrace (prefixWord ++ tailWord_468282) baseStart_468282 baseEnd_468282 := by
    simpa [prefixWord, tailWord_468282, baseEnd_468282] using wordTrace_append hprefix tailTrace_468282
  have hstable : (prefixWord ++ tailWord_468282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468282).length < 2 ^ (prefixWord ++ tailWord_468282).sum := by decide
  have hdescent : baseEnd_468282 < baseStart_468282 := by decide
  rcases family_descends (prefixWord ++ tailWord_468282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468583 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_468583 : Nat := 118140960795 + 468583 * 2 ^ 59
def prefixEnd_468583 : Nat := 4983230072969 + 3 ^ 40 * 468583 * 2
def baseEnd_468583 : Nat := 106937024678153511358903

theorem tailTrace_468583 : CollatzResearch.WordTrace tailWord_468583 prefixEnd_468583 106937024678153511358903 := by
  unfold tailWord_468583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090626061411293450186403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11393750707607528966790935 17090626061411293450186403)
  ·
    refine ⟨25635939092116940175279605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17090626061411293450186403 25635939092116940175279605)
    ·
      refine ⟨2403369289885963141432463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25635939092116940175279605 2403369289885963141432463)
      ·
        refine ⟨3605053934828944712148695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403369289885963141432463 3605053934828944712148695)
        ·
          refine ⟨5407580902243417068223043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605053934828944712148695 5407580902243417068223043)
          ·
            refine ⟨8111371353365125602334565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407580902243417068223043 8111371353365125602334565)
            ·
              refine ⟨1520882128755961050437731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8111371353365125602334565 1520882128755961050437731)
              ·
                refine ⟨2281323193133941575656597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520882128755961050437731 2281323193133941575656597)
                ·
                  refine ⟨106937024678153511358903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2281323193133941575656597 106937024678153511358903)
                  ·
                    rfl

theorem cell21_468583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_468583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468583 prefixEnd_468583 := by exact prefixLift 468583
  have htrace : WordTrace (prefixWord ++ tailWord_468583) baseStart_468583 baseEnd_468583 := by
    simpa [prefixWord, tailWord_468583, baseEnd_468583] using wordTrace_append hprefix tailTrace_468583
  have hstable : (prefixWord ++ tailWord_468583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468583).length < 2 ^ (prefixWord ++ tailWord_468583).sum := by decide
  have hdescent : baseEnd_468583 < baseStart_468583 := by decide
  rcases family_descends (prefixWord ++ tailWord_468583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468586 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_468586 : Nat := 118140960795 + 468586 * 2 ^ 59
def prefixEnd_468586 : Nat := 4983230072969 + 3 ^ 40 * 468586 * 2
def baseEnd_468586 : Nat := 106937709319026172808897

theorem tailTrace_468586 : CollatzResearch.WordTrace tailWord_468586 prefixEnd_468586 106937709319026172808897 := by
  unfold tailWord_468586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272683870100106240636403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11393823653600283308363741 4272683870100106240636403)
  ·
    refine ⟨6409025805150159360954605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4272683870100106240636403 6409025805150159360954605)
    ·
      refine ⟨2403384676931309760357977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6409025805150159360954605 2403384676931309760357977)
      ·
        refine ⟨1802538507698482320268483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403384676931309760357977 1802538507698482320268483)
        ·
          refine ⟨2703807761547723480402725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802538507698482320268483 2703807761547723480402725)
          ·
            refine ⟨506963955290198152575511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2703807761547723480402725 506963955290198152575511)
            ·
              refine ⟨760445932935297228863267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506963955290198152575511 760445932935297228863267)
              ·
                refine ⟨1140668899402945843294901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760445932935297228863267 1140668899402945843294901)
                ·
                  refine ⟨106937709319026172808897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1140668899402945843294901 106937709319026172808897)
                  ·
                    rfl

theorem cell21_468586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_468586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468586 prefixEnd_468586 := by exact prefixLift 468586
  have htrace : WordTrace (prefixWord ++ tailWord_468586) baseStart_468586 baseEnd_468586 := by
    simpa [prefixWord, tailWord_468586, baseEnd_468586] using wordTrace_append hprefix tailTrace_468586
  have hstable : (prefixWord ++ tailWord_468586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468586).length < 2 ^ (prefixWord ++ tailWord_468586).sum := by decide
  have hdescent : baseEnd_468586 < baseStart_468586 := by decide
  rcases family_descends (prefixWord ++ tailWord_468586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468659 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_468659 : Nat := 118140960795 + 468659 * 2 ^ 59
def prefixEnd_468659 : Nat := 4983230072969 + 3 ^ 40 * 468659 * 2
def baseEnd_468659 : Nat := 106954368913594268092081

theorem tailTrace_468659 : CollatzResearch.WordTrace tailWord_468659 prefixEnd_468659 106954368913594268092081 := by
  unfold tailWord_468659
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093398009135958429953031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11395598672757305619968687 17093398009135958429953031)
  ·
    refine ⟨25640097013703937644929547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17093398009135958429953031 25640097013703937644929547)
    ·
      refine ⟨38460145520555906467394321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25640097013703937644929547 38460145520555906467394321)
      ·
        refine ⟨28845109140416929850545741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38460145520555906467394321 28845109140416929850545741)
        ·
          refine ⟨10816915927656348693954653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28845109140416929850545741 10816915927656348693954653)
          ·
            refine ⟨4056343472871130760232995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10816915927656348693954653 4056343472871130760232995)
            ·
              refine ⟨6084515209306696140349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056343472871130760232995 6084515209306696140349493)
              ·
                refine ⟨570423300872502763157765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6084515209306696140349493 570423300872502763157765)
                ·
                  refine ⟨106954368913594268092081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570423300872502763157765 106954368913594268092081)
                  ·
                    rfl

theorem cell21_468659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_468659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468659 prefixEnd_468659 := by exact prefixLift 468659
  have htrace : WordTrace (prefixWord ++ tailWord_468659) baseStart_468659 baseEnd_468659 := by
    simpa [prefixWord, tailWord_468659, baseEnd_468659] using wordTrace_append hprefix tailTrace_468659
  have hstable : (prefixWord ++ tailWord_468659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468659).length < 2 ^ (prefixWord ++ tailWord_468659).sum := by decide
  have hdescent : baseEnd_468659 < baseStart_468659 := by decide
  rcases family_descends (prefixWord ++ tailWord_468659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468662 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_468662 : Nat := 118140960795 + 468662 * 2 ^ 59
def prefixEnd_468662 : Nat := 4983230072969 + 3 ^ 40 * 468662 * 2
def baseEnd_468662 : Nat := 106955053554466929542075

theorem tailTrace_468662 : CollatzResearch.WordTrace tailWord_468662 prefixEnd_468662 106955053554466929542075 := by
  unfold tailWord_468662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068344214257818121394515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11395671618750059961541493 1068344214257818121394515)
  ·
    refine ⟨1602516321386727182091773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068344214257818121394515 1602516321386727182091773)
    ·
      refine ⟨600943620520022693284415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1602516321386727182091773 600943620520022693284415)
      ·
        refine ⟨901415430780034039926623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600943620520022693284415 901415430780034039926623)
        ·
          refine ⟨1352123146170051059889935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901415430780034039926623 1352123146170051059889935)
          ·
            refine ⟨2028184719255076589834903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352123146170051059889935 2028184719255076589834903)
            ·
              refine ⟨3042277078882614884752355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028184719255076589834903 3042277078882614884752355)
              ·
                refine ⟨4563415618323922327128533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042277078882614884752355 4563415618323922327128533)
                ·
                  refine ⟨106955053554466929542075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4563415618323922327128533 106955053554466929542075)
                  ·
                    rfl

theorem cell21_468662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_468662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468662 prefixEnd_468662 := by exact prefixLift 468662
  have htrace : WordTrace (prefixWord ++ tailWord_468662) baseStart_468662 baseEnd_468662 := by
    simpa [prefixWord, tailWord_468662, baseEnd_468662] using wordTrace_append hprefix tailTrace_468662
  have hstable : (prefixWord ++ tailWord_468662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468662).length < 2 ^ (prefixWord ++ tailWord_468662).sum := by decide
  have hdescent : baseEnd_468662 < baseStart_468662 := by decide
  rcases family_descends (prefixWord ++ tailWord_468662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468690 : List Nat := [3, 2, 2, 2, 2, 2, 8]
def baseStart_468690 : Nat := 118140960795 + 468690 * 2 ^ 59
def prefixEnd_468690 : Nat := 4983230072969 + 3 ^ 40 * 468690 * 2
def baseEnd_468690 : Nat := 11884604837327233675039

theorem tailTrace_468690 : CollatzResearch.WordTrace tailWord_468690 prefixEnd_468690 11884604837327233675039 := by
  unfold tailWord_468690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273632168005912681082881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11396352448015767149554349 4273632168005912681082881)
  ·
    refine ⟨3205224126004434510812161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4273632168005912681082881 3205224126004434510812161)
    ·
      refine ⟨2403918094503325883109121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205224126004434510812161 2403918094503325883109121)
      ·
        refine ⟨1802938570877494412331841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403918094503325883109121 1802938570877494412331841)
        ·
          refine ⟨1352203928158120809248881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802938570877494412331841 1352203928158120809248881)
          ·
            refine ⟨1014152946118590606936661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352203928158120809248881 1014152946118590606936661)
            ·
              refine ⟨11884604837327233675039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1014152946118590606936661 11884604837327233675039)
              ·
                rfl

theorem cell21_468690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 8].length) (baseStart_468690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468690 prefixEnd_468690 := by exact prefixLift 468690
  have htrace : WordTrace (prefixWord ++ tailWord_468690) baseStart_468690 baseEnd_468690 := by
    simpa [prefixWord, tailWord_468690, baseEnd_468690] using wordTrace_append hprefix tailTrace_468690
  have hstable : (prefixWord ++ tailWord_468690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468690).length < 2 ^ (prefixWord ++ tailWord_468690).sum := by decide
  have hdescent : baseEnd_468690 < baseStart_468690 := by decide
  rcases family_descends (prefixWord ++ tailWord_468690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468704 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_468704 : Nat := 118140960795 + 468704 * 2 ^ 59
def prefixEnd_468704 : Nat := 4983230072969 + 3 ^ 40 * 468704 * 2
def baseEnd_468704 : Nat := 106964638526684189841989

theorem tailTrace_468704 : CollatzResearch.WordTrace tailWord_468704 prefixEnd_468704 106964638526684189841989 := by
  unfold tailWord_468704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547519646986465557670583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11396692862648620743560777 8547519646986465557670583)
  ·
    refine ⟨12821279470479698336505875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547519646986465557670583 12821279470479698336505875)
    ·
      refine ⟨19231919205719547504758813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821279470479698336505875 19231919205719547504758813)
      ·
        refine ⟨7211969702144830314284555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19231919205719547504758813 7211969702144830314284555)
        ·
          refine ⟨10817954553217245471426833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211969702144830314284555 10817954553217245471426833)
          ·
            refine ⟨8113465914912934103570125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10817954553217245471426833 8113465914912934103570125)
            ·
              refine ⟨3042549718092350288838797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8113465914912934103570125 3042549718092350288838797)
              ·
                refine ⟨1140956144284631358314549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3042549718092350288838797 1140956144284631358314549)
                ·
                  refine ⟨106964638526684189841989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1140956144284631358314549 106964638526684189841989)
                  ·
                    rfl

theorem cell21_468704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_468704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468704 prefixEnd_468704 := by exact prefixLift 468704
  have htrace : WordTrace (prefixWord ++ tailWord_468704) baseStart_468704 baseEnd_468704 := by
    simpa [prefixWord, tailWord_468704, baseEnd_468704] using wordTrace_append hprefix tailTrace_468704
  have hstable : (prefixWord ++ tailWord_468704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468704).length < 2 ^ (prefixWord ++ tailWord_468704).sum := by decide
  have hdescent : baseEnd_468704 < baseStart_468704 := by decide
  rcases family_descends (prefixWord ++ tailWord_468704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468724 : List Nat := [2, 6, 1, 1, 1, 2, 1, 7]
def baseStart_468724 : Nat := 118140960795 + 468724 * 2 ^ 59
def prefixEnd_468724 : Nat := 4983230072969 + 3 ^ 40 * 468724 * 2
def baseEnd_468724 : Nat := 35656400933056199836205

theorem tailTrace_468724 : CollatzResearch.WordTrace tailWord_468724 prefixEnd_468724 35656400933056199836205 := by
  unfold tailWord_468724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547884376950237265534613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11397179169266983020712817 8547884376950237265534613)
  ·
    refine ⟨400682080169542371821935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8547884376950237265534613 400682080169542371821935)
    ·
      refine ⟨601023120254313557732903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400682080169542371821935 601023120254313557732903)
      ·
        refine ⟨901534680381470336599355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601023120254313557732903 901534680381470336599355)
        ·
          refine ⟨1352302020572205504899033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901534680381470336599355 1352302020572205504899033)
          ·
            refine ⟨1014226515429154128674275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352302020572205504899033 1014226515429154128674275)
            ·
              refine ⟨1521339773143731193011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014226515429154128674275 1521339773143731193011413)
              ·
                refine ⟨35656400933056199836205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1521339773143731193011413 35656400933056199836205)
                ·
                  rfl

theorem cell21_468724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_468724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468724 prefixEnd_468724 := by exact prefixLift 468724
  have htrace : WordTrace (prefixWord ++ tailWord_468724) baseStart_468724 baseEnd_468724 := by
    simpa [prefixWord, tailWord_468724, baseEnd_468724] using wordTrace_append hprefix tailTrace_468724
  have hstable : (prefixWord ++ tailWord_468724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468724).length < 2 ^ (prefixWord ++ tailWord_468724).sum := by decide
  have hdescent : baseEnd_468724 < baseStart_468724 := by decide
  rcases family_descends (prefixWord ++ tailWord_468724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468769 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 4]
def baseStart_468769 : Nat := 118140960795 + 468769 * 2 ^ 59
def prefixEnd_468769 : Nat := 4983230072969 + 3 ^ 40 * 468769 * 2
def baseEnd_468769 : Nat := 106979472412258521258523

theorem tailTrace_468769 : CollatzResearch.WordTrace tailWord_468769 prefixEnd_468769 106979472412258521258523 := by
  unfold tailWord_468769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097410038737447216457361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11398273359158298144304907 17097410038737447216457361)
  ·
    refine ⟨12823057529053085412343021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17097410038737447216457361 12823057529053085412343021)
    ·
      refine ⟨4808646573394907029628633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12823057529053085412343021 4808646573394907029628633)
      ·
        refine ⟨3606484930046180272221475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808646573394907029628633 3606484930046180272221475)
        ·
          refine ⟨5409727395069270408332213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606484930046180272221475 5409727395069270408332213)
          ·
            refine ⟨507161943287744100781145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5409727395069270408332213 507161943287744100781145)
            ·
              refine ⟨380371457465808075585859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507161943287744100781145 380371457465808075585859)
              ·
                refine ⟨570557186198712113378789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380371457465808075585859 570557186198712113378789)
                ·
                  refine ⟨106979472412258521258523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570557186198712113378789 106979472412258521258523)
                  ·
                    rfl

theorem cell21_468769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_468769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468769 prefixEnd_468769 := by exact prefixLift 468769
  have htrace : WordTrace (prefixWord ++ tailWord_468769) baseStart_468769 baseEnd_468769 := by
    simpa [prefixWord, tailWord_468769, baseEnd_468769] using wordTrace_append hprefix tailTrace_468769
  have hstable : (prefixWord ++ tailWord_468769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468769).length < 2 ^ (prefixWord ++ tailWord_468769).sum := by decide
  have hdescent : baseEnd_468769 < baseStart_468769 := by decide
  rcases family_descends (prefixWord ++ tailWord_468769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468862 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_468862 : Nat := 118140960795 + 468862 * 2 ^ 59
def prefixEnd_468862 : Nat := 4983230072969 + 3 ^ 40 * 468862 * 2
def baseEnd_468862 : Nat := 107000696279311026208333

theorem tailTrace_468862 : CollatzResearch.WordTrace tailWord_468862 prefixEnd_468862 107000696279311026208333 := by
  unfold tailWord_468862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137600253425065512449105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11400534684933682733061893 2137600253425065512449105)
  ·
    refine ⟨1603200190068799134336829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2137600253425065512449105 1603200190068799134336829)
    ·
      refine ⟨601200071275799675376311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1603200190068799134336829 601200071275799675376311)
      ·
        refine ⟨901800106913699513064467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601200071275799675376311 901800106913699513064467)
        ·
          refine ⟨1352700160370549269596701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901800106913699513064467 1352700160370549269596701)
          ·
            refine ⟨507262560138955976098763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1352700160370549269596701 507262560138955976098763)
            ·
              refine ⟨760893840208433964148145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507262560138955976098763 760893840208433964148145)
              ·
                refine ⟨570670380156325473111109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760893840208433964148145 570670380156325473111109)
                ·
                  refine ⟨107000696279311026208333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570670380156325473111109 107000696279311026208333)
                  ·
                    rfl

theorem cell21_468862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_468862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468862 prefixEnd_468862 := by exact prefixLift 468862
  have htrace : WordTrace (prefixWord ++ tailWord_468862) baseStart_468862 baseEnd_468862 := by
    simpa [prefixWord, tailWord_468862, baseEnd_468862] using wordTrace_append hprefix tailTrace_468862
  have hstable : (prefixWord ++ tailWord_468862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468862).length < 2 ^ (prefixWord ++ tailWord_468862).sum := by decide
  have hdescent : baseEnd_468862 < baseStart_468862 := by decide
  rcases family_descends (prefixWord ++ tailWord_468862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468873 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 3]
def baseStart_468873 : Nat := 118140960795 + 468873 * 2 ^ 59
def prefixEnd_468873 : Nat := 4983230072969 + 3 ^ 40 * 468873 * 2
def baseEnd_468873 : Nat := 107003206629177451524977

theorem tailTrace_468873 : CollatzResearch.WordTrace tailWord_468873 prefixEnd_468873 107003206629177451524977 := by
  unfold tailWord_468873
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101203230360672978243273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11400802153573781985495515 17101203230360672978243273)
  ·
    refine ⟨12825902422770504733682455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17101203230360672978243273 12825902422770504733682455)
    ·
      refine ⟨19238853634155757100523683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12825902422770504733682455 19238853634155757100523683)
      ·
        refine ⟨28858280451233635650785525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19238853634155757100523683 28858280451233635650785525)
        ·
          refine ⟨2705463792303153342261143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28858280451233635650785525 2705463792303153342261143)
          ·
            refine ⟨4058195688454730013391715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705463792303153342261143 4058195688454730013391715)
            ·
              refine ⟨6087293532682095020087573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058195688454730013391715 6087293532682095020087573)
              ·
                refine ⟨285341884344473204066605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6087293532682095020087573 285341884344473204066605)
                ·
                  refine ⟨107003206629177451524977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285341884344473204066605 107003206629177451524977)
                  ·
                    rfl

theorem cell21_468873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_468873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468873 prefixEnd_468873 := by exact prefixLift 468873
  have htrace : WordTrace (prefixWord ++ tailWord_468873) baseStart_468873 baseEnd_468873 := by
    simpa [prefixWord, tailWord_468873, baseEnd_468873] using wordTrace_append hprefix tailTrace_468873
  have hstable : (prefixWord ++ tailWord_468873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468873).length < 2 ^ (prefixWord ++ tailWord_468873).sum := by decide
  have hdescent : baseEnd_468873 < baseStart_468873 := by decide
  rcases family_descends (prefixWord ++ tailWord_468873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468924 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_468924 : Nat := 118140960795 + 468924 * 2 ^ 59
def prefixEnd_468924 : Nat := 4983230072969 + 3 ^ 40 * 468924 * 2
def baseEnd_468924 : Nat := 107014845524012696174873

theorem tailTrace_468924 : CollatzResearch.WordTrace tailWord_468924 prefixEnd_468924 107014845524012696174873 := by
  unfold tailWord_468924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551531676587954344174913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11402042235450605792233217 8551531676587954344174913)
  ·
    refine ⟨6413648757440965758131185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8551531676587954344174913 6413648757440965758131185)
    ·
      refine ⟨4810236568080724318598389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413648757440965758131185 4810236568080724318598389)
      ·
        refine ⟨450959678257567904868599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4810236568080724318598389 450959678257567904868599)
        ·
          refine ⟨676439517386351857302899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450959678257567904868599 676439517386351857302899)
          ·
            refine ⟨1014659276079527785954349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676439517386351857302899 1014659276079527785954349)
            ·
              refine ⟨380497228529822919732881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014659276079527785954349 380497228529822919732881)
              ·
                refine ⟨285372921397367189799661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380497228529822919732881 285372921397367189799661)
                ·
                  refine ⟨107014845524012696174873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285372921397367189799661 107014845524012696174873)
                  ·
                    rfl

theorem cell21_468924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_468924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468924 prefixEnd_468924 := by exact prefixLift 468924
  have htrace : WordTrace (prefixWord ++ tailWord_468924) baseStart_468924 baseEnd_468924 := by
    simpa [prefixWord, tailWord_468924, baseEnd_468924] using wordTrace_append hprefix tailTrace_468924
  have hstable : (prefixWord ++ tailWord_468924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468924).length < 2 ^ (prefixWord ++ tailWord_468924).sum := by decide
  have hdescent : baseEnd_468924 < baseStart_468924 := by decide
  rcases family_descends (prefixWord ++ tailWord_468924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468977 : List Nat := [1, 2, 2, 2, 5, 9]
def baseStart_468977 : Nat := 118140960795 + 468977 * 2 ^ 59
def prefixEnd_468977 : Nat := 4983230072969 + 3 ^ 40 * 468977 * 2
def baseEnd_468977 : Nat := 3963960772077643770053

theorem tailTrace_468977 : CollatzResearch.WordTrace tailWord_468977 prefixEnd_468977 3963960772077643770053 := by
  unfold tailWord_468977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104996421983898740029185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11403330947989265826686123 17104996421983898740029185)
  ·
    refine ⟨12828747316487924055021889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17104996421983898740029185 12828747316487924055021889)
    ·
      refine ⟨9621560487365943041266417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828747316487924055021889 9621560487365943041266417)
      ·
        refine ⟨7216170365524457280949813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9621560487365943041266417 7216170365524457280949813)
        ·
          refine ⟨676515971767917870089045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7216170365524457280949813 676515971767917870089045)
          ·
            refine ⟨3963960772077643770053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 676515971767917870089045 3963960772077643770053)
            ·
              rfl

theorem cell21_468977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 9].length) (baseStart_468977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468977 prefixEnd_468977 := by exact prefixLift 468977
  have htrace : WordTrace (prefixWord ++ tailWord_468977) baseStart_468977 baseEnd_468977 := by
    simpa [prefixWord, tailWord_468977, baseEnd_468977] using wordTrace_append hprefix tailTrace_468977
  have hstable : (prefixWord ++ tailWord_468977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468977).length < 2 ^ (prefixWord ++ tailWord_468977).sum := by decide
  have hdescent : baseEnd_468977 < baseStart_468977 := by decide
  rcases family_descends (prefixWord ++ tailWord_468977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468991 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_468991 : Nat := 118140960795 + 468991 * 2 ^ 59
def prefixEnd_468991 : Nat := 4983230072969 + 3 ^ 40 * 468991 * 2
def baseEnd_468991 : Nat := 107030135836835468558069

theorem tailTrace_468991 : CollatzResearch.WordTrace tailWord_468991 prefixEnd_468991 107030135836835468558069 := by
  unfold tailWord_468991
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105507043933179131038827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11403671362622119420692551 17105507043933179131038827)
  ·
    refine ⟨25658260565899768696558241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17105507043933179131038827 25658260565899768696558241)
    ·
      refine ⟨19243695424424826522418681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25658260565899768696558241 19243695424424826522418681)
      ·
        refine ⟨14432771568318619891814011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19243695424424826522418681 14432771568318619891814011)
        ·
          refine ⟨21649157352477929837721017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14432771568318619891814011 21649157352477929837721017)
          ·
            refine ⟨16236868014358447378290763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21649157352477929837721017 16236868014358447378290763)
            ·
              refine ⟨24355302021537671067436145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236868014358447378290763 24355302021537671067436145)
              ·
                refine ⟨18266476516153253300577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24355302021537671067436145 18266476516153253300577109)
                ·
                  refine ⟨107030135836835468558069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18266476516153253300577109 107030135836835468558069)
                  ·
                    rfl

theorem cell21_468991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_468991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_468991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_468991 prefixEnd_468991 := by exact prefixLift 468991
  have htrace : WordTrace (prefixWord ++ tailWord_468991) baseStart_468991 baseEnd_468991 := by
    simpa [prefixWord, tailWord_468991, baseEnd_468991] using wordTrace_append hprefix tailTrace_468991
  have hstable : (prefixWord ++ tailWord_468991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468991).length < 2 ^ (prefixWord ++ tailWord_468991).sum := by decide
  have hdescent : baseEnd_468991 < baseStart_468991 := by decide
  rcases family_descends (prefixWord ++ tailWord_468991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469053 : List Nat := [1, 4, 1, 3, 1, 1, 2, 8]
def baseStart_469053 : Nat := 118140960795 + 469053 * 2 ^ 59
def prefixEnd_469053 : Nat := 4983230072969 + 3 ^ 40 * 469053 * 2
def baseEnd_469053 : Nat := 35681428360512379508203

theorem tailTrace_469053 : CollatzResearch.WordTrace tailWord_469053 prefixEnd_469053 35681428360512379508203 := by
  unfold tailWord_469053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107768369708563719795813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11405178913139042479863875 17107768369708563719795813)
  ·
    refine ⟨3207706569320355697461715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17107768369708563719795813 3207706569320355697461715)
    ·
      refine ⟨4811559853980533546192573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207706569320355697461715 4811559853980533546192573)
      ·
        refine ⟨1804334945242700079822215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4811559853980533546192573 1804334945242700079822215)
        ·
          refine ⟨2706502417864050119733323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804334945242700079822215 2706502417864050119733323)
          ·
            refine ⟨4059753626796075179599985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706502417864050119733323 4059753626796075179599985)
            ·
              refine ⟨3044815220097056384699989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4059753626796075179599985 3044815220097056384699989)
              ·
                refine ⟨35681428360512379508203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3044815220097056384699989 35681428360512379508203)
                ·
                  rfl

theorem cell21_469053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_469053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469053 prefixEnd_469053 := by exact prefixLift 469053
  have htrace : WordTrace (prefixWord ++ tailWord_469053) baseStart_469053 baseEnd_469053 := by
    simpa [prefixWord, tailWord_469053, baseEnd_469053] using wordTrace_append hprefix tailTrace_469053
  have hstable : (prefixWord ++ tailWord_469053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469053).length < 2 ^ (prefixWord ++ tailWord_469053).sum := by decide
  have hdescent : baseEnd_469053 < baseStart_469053 := by decide
  rcases family_descends (prefixWord ++ tailWord_469053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469056 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_469056 : Nat := 118140960795 + 469056 * 2 ^ 59
def prefixEnd_469056 : Nat := 4983230072969 + 3 ^ 40 * 469056 * 2
def baseEnd_469056 : Nat := 107044969722409799974603

theorem tailTrace_469056 : CollatzResearch.WordTrace tailWord_469056 prefixEnd_469056 107044969722409799974603 := by
  unfold tailWord_469056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553938894348847616077511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11405251859131796821436681 8553938894348847616077511)
  ·
    refine ⟨12830908341523271424116267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8553938894348847616077511 12830908341523271424116267)
    ·
      refine ⟨19246362512284907136174401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12830908341523271424116267 19246362512284907136174401)
      ·
        refine ⟨14434771884213680352130801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19246362512284907136174401 14434771884213680352130801)
        ·
          refine ⟨10826078913160260264098101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14434771884213680352130801 10826078913160260264098101)
          ·
            refine ⟨1014944898108774399759197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10826078913160260264098101 1014944898108774399759197)
            ·
              refine ⟨380604336790790399909699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014944898108774399759197 380604336790790399909699)
              ·
                refine ⟨570906505186185599864549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380604336790790399909699 570906505186185599864549)
                ·
                  refine ⟨107044969722409799974603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570906505186185599864549 107044969722409799974603)
                  ·
                    rfl

theorem cell21_469056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_469056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469056 prefixEnd_469056 := by exact prefixLift 469056
  have htrace : WordTrace (prefixWord ++ tailWord_469056) baseStart_469056 baseEnd_469056 := by
    simpa [prefixWord, tailWord_469056, baseEnd_469056] using wordTrace_append hprefix tailTrace_469056
  have hstable : (prefixWord ++ tailWord_469056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469056).length < 2 ^ (prefixWord ++ tailWord_469056).sum := by decide
  have hdescent : baseEnd_469056 < baseStart_469056 := by decide
  rcases family_descends (prefixWord ++ tailWord_469056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469070 : List Nat := [4, 1, 1, 1, 1, 4, 4, 5]
def baseStart_469070 : Nat := 118140960795 + 469070 * 2 ^ 59
def prefixEnd_469070 : Nat := 4983230072969 + 3 ^ 40 * 469070 * 2
def baseEnd_469070 : Nat := 35682721571049628913747

theorem tailTrace_469070 : CollatzResearch.WordTrace tailWord_469070 prefixEnd_469070 35682721571049628913747 := by
  unfold tailWord_469070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138548551330871952895583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11405592273764650415443109 2138548551330871952895583)
  ·
    refine ⟨3207822826996307929343375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138548551330871952895583 3207822826996307929343375)
    ·
      refine ⟨4811734240494461894015063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207822826996307929343375 4811734240494461894015063)
      ·
        refine ⟨7217601360741692841022595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811734240494461894015063 7217601360741692841022595)
        ·
          refine ⟨10826402041112539261533893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217601360741692841022595 10826402041112539261533893)
          ·
            refine ⟨2029950382708601111537605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10826402041112539261533893 2029950382708601111537605)
            ·
              refine ⟨380615696757862708413301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2029950382708601111537605 380615696757862708413301)
              ·
                refine ⟨35682721571049628913747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380615696757862708413301 35682721571049628913747)
                ·
                  rfl

theorem cell21_469070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_469070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469070 prefixEnd_469070 := by exact prefixLift 469070
  have htrace : WordTrace (prefixWord ++ tailWord_469070) baseStart_469070 baseEnd_469070 := by
    simpa [prefixWord, tailWord_469070, baseEnd_469070] using wordTrace_append hprefix tailTrace_469070
  have hstable : (prefixWord ++ tailWord_469070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469070).length < 2 ^ (prefixWord ++ tailWord_469070).sum := by decide
  have hdescent : baseEnd_469070 < baseStart_469070 := by decide
  rcases family_descends (prefixWord ++ tailWord_469070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469146 : List Nat := [3, 1, 1, 5, 3, 8]
def baseStart_469146 : Nat := 118140960795 + 469146 * 2 ^ 59
def prefixEnd_469146 : Nat := 4983230072969 + 3 ^ 40 * 469146 * 2
def baseEnd_469146 : Nat := 3965389220318134943497

theorem tailTrace_469146 : CollatzResearch.WordTrace tailWord_469146 prefixEnd_469146 3965389220318134943497 := by
  unfold tailWord_469146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277790089592910150732823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11407440238914427068620861 4277790089592910150732823)
  ·
    refine ⟨6416685134389365226099235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277790089592910150732823 6416685134389365226099235)
    ·
      refine ⟨9625027701584047839148853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416685134389365226099235 9625027701584047839148853)
      ·
        refine ⟨902346347023504484920205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9625027701584047839148853 902346347023504484920205)
        ·
          refine ⟨338379880133814181845077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902346347023504484920205 338379880133814181845077)
          ·
            refine ⟨3965389220318134943497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 338379880133814181845077 3965389220318134943497)
            ·
              rfl

theorem cell21_469146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 8].length) (baseStart_469146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469146 prefixEnd_469146 := by exact prefixLift 469146
  have htrace : WordTrace (prefixWord ++ tailWord_469146) baseStart_469146 baseEnd_469146 := by
    simpa [prefixWord, tailWord_469146, baseEnd_469146] using wordTrace_append hprefix tailTrace_469146
  have hstable : (prefixWord ++ tailWord_469146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469146).length < 2 ^ (prefixWord ++ tailWord_469146).sum := by decide
  have hdescent : baseEnd_469146 < baseStart_469146 := by decide
  rcases family_descends (prefixWord ++ tailWord_469146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469208 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_469208 : Nat := 118140960795 + 469208 * 2 ^ 59
def prefixEnd_469208 : Nat := 4983230072969 + 3 ^ 40 * 469208 * 2
def baseEnd_469208 : Nat := 107079658193291313440959

theorem tailTrace_469208 : CollatzResearch.WordTrace tailWord_469208 prefixEnd_469208 107079658193291313440959 := by
  unfold tailWord_469208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556710842073512595844139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11408947789431350127792185 8556710842073512595844139)
  ·
    refine ⟨12835066263110268893766209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556710842073512595844139 12835066263110268893766209)
    ·
      refine ⟨9626299697332701670324657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835066263110268893766209 9626299697332701670324657)
      ·
        refine ⟨7219724772999526252743493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9626299697332701670324657 7219724772999526252743493)
        ·
          refine ⟨1353698394937411172389405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7219724772999526252743493 1353698394937411172389405)
          ·
            refine ⟨507636898101529189646027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353698394937411172389405 507636898101529189646027)
            ·
              refine ⟨761455347152293784469041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507636898101529189646027 761455347152293784469041)
              ·
                refine ⟨571091510364220338351781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761455347152293784469041 571091510364220338351781)
                ·
                  refine ⟨107079658193291313440959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571091510364220338351781 107079658193291313440959)
                  ·
                    rfl

theorem cell21_469208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_469208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469208 prefixEnd_469208 := by exact prefixLift 469208
  have htrace : WordTrace (prefixWord ++ tailWord_469208) baseStart_469208 baseEnd_469208 := by
    simpa [prefixWord, tailWord_469208, baseEnd_469208] using wordTrace_append hprefix tailTrace_469208
  have hstable : (prefixWord ++ tailWord_469208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469208).length < 2 ^ (prefixWord ++ tailWord_469208).sum := by decide
  have hdescent : baseEnd_469208 < baseStart_469208 := by decide
  rcases family_descends (prefixWord ++ tailWord_469208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469284 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_469284 : Nat := 118140960795 + 469284 * 2 ^ 59
def prefixEnd_469284 : Nat := 4983230072969 + 3 ^ 40 * 469284 * 2
def baseEnd_469284 : Nat := 107097002428732070174137

theorem tailTrace_469284 : CollatzResearch.WordTrace tailWord_469284 prefixEnd_469284 107097002428732070174137 := by
  unfold tailWord_469284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558096815935845085727453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11410795754581126780969937 8558096815935845085727453)
  ·
    refine ⟨3209286305975941907147795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8558096815935845085727453 3209286305975941907147795)
    ·
      refine ⟨4813929458963912860721693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209286305975941907147795 4813929458963912860721693)
      ·
        refine ⟨1805223547111467322770635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4813929458963912860721693 1805223547111467322770635)
        ·
          refine ⟨2707835320667200984155953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805223547111467322770635 2707835320667200984155953)
          ·
            refine ⟨2030876490500400738116965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707835320667200984155953 2030876490500400738116965)
            ·
              refine ⟨380789341968825138396931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2030876490500400738116965 380789341968825138396931)
              ·
                refine ⟨571184012953237707595397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380789341968825138396931 571184012953237707595397)
                ·
                  refine ⟨107097002428732070174137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571184012953237707595397 107097002428732070174137)
                  ·
                    rfl

theorem cell21_469284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_469284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469284 prefixEnd_469284 := by exact prefixLift 469284
  have htrace : WordTrace (prefixWord ++ tailWord_469284) baseStart_469284 baseEnd_469284 := by
    simpa [prefixWord, tailWord_469284, baseEnd_469284] using wordTrace_append hprefix tailTrace_469284
  have hstable : (prefixWord ++ tailWord_469284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469284).length < 2 ^ (prefixWord ++ tailWord_469284).sum := by decide
  have hdescent : baseEnd_469284 < baseStart_469284 := by decide
  rcases family_descends (prefixWord ++ tailWord_469284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469295 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_469295 : Nat := 118140960795 + 469295 * 2 ^ 59
def prefixEnd_469295 : Nat := 4983230072969 + 3 ^ 40 * 469295 * 2
def baseEnd_469295 : Nat := 107099512778598495490781

theorem tailTrace_469295 : CollatzResearch.WordTrace tailWord_469295 prefixEnd_469295 107099512778598495490781 := by
  unfold tailWord_469295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116594834831839050105339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11411063223221226033403559 17116594834831839050105339)
  ·
    refine ⟨25674892252247758575158009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17116594834831839050105339 25674892252247758575158009)
    ·
      refine ⟨19256169189185818931368507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25674892252247758575158009 19256169189185818931368507)
      ·
        refine ⟨28884253783778728397052761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19256169189185818931368507 28884253783778728397052761)
        ·
          refine ⟨21663190337834046297789571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28884253783778728397052761 21663190337834046297789571)
          ·
            refine ⟨32494785506751069446684357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21663190337834046297789571 32494785506751069446684357)
            ·
              refine ⟨6092772282515825521253317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32494785506751069446684357 6092772282515825521253317)
              ·
                refine ⟨1142394802971717285234997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6092772282515825521253317 1142394802971717285234997)
                ·
                  refine ⟨107099512778598495490781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142394802971717285234997 107099512778598495490781)
                  ·
                    rfl

theorem cell21_469295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_469295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469295 prefixEnd_469295 := by exact prefixLift 469295
  have htrace : WordTrace (prefixWord ++ tailWord_469295) baseStart_469295 baseEnd_469295 := by
    simpa [prefixWord, tailWord_469295, baseEnd_469295] using wordTrace_append hprefix tailTrace_469295
  have hstable : (prefixWord ++ tailWord_469295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469295).length < 2 ^ (prefixWord ++ tailWord_469295).sum := by decide
  have hdescent : baseEnd_469295 < baseStart_469295 := by decide
  rcases family_descends (prefixWord ++ tailWord_469295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469329 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 3]
def baseStart_469329 : Nat := 118140960795 + 469329 * 2 ^ 59
def prefixEnd_469329 : Nat := 4983230072969 + 3 ^ 40 * 469329 * 2
def baseEnd_469329 : Nat := 107107272041821991924045

theorem tailTrace_469329 : CollatzResearch.WordTrace tailWord_469329 prefixEnd_469329 107107272041821991924045 := by
  unfold tailWord_469329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17117834916708662856843041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11411889944472441904562027 17117834916708662856843041)
  ·
    refine ⟨12838376187531497142632281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17117834916708662856843041 12838376187531497142632281)
    ·
      refine ⟨9628782140648622856974211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12838376187531497142632281 9628782140648622856974211)
      ·
        refine ⟨14443173210972934285461317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628782140648622856974211 14443173210972934285461317)
        ·
          refine ⟨2708094977057425178523997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14443173210972934285461317 2708094977057425178523997)
          ·
            refine ⟨1015535616396534441946499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2708094977057425178523997 1015535616396534441946499)
            ·
              refine ⟨1523303424594801662919749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015535616396534441946499 1523303424594801662919749)
              ·
                refine ⟨285619392111525311797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1523303424594801662919749 285619392111525311797453)
                ·
                  refine ⟨107107272041821991924045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285619392111525311797453 107107272041821991924045)
                  ·
                    rfl

theorem cell21_469329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_469329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469329 prefixEnd_469329 := by exact prefixLift 469329
  have htrace : WordTrace (prefixWord ++ tailWord_469329) baseStart_469329 baseEnd_469329 := by
    simpa [prefixWord, tailWord_469329, baseEnd_469329] using wordTrace_append hprefix tailTrace_469329
  have hstable : (prefixWord ++ tailWord_469329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469329).length < 2 ^ (prefixWord ++ tailWord_469329).sum := by decide
  have hdescent : baseEnd_469329 < baseStart_469329 := by decide
  rcases family_descends (prefixWord ++ tailWord_469329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469388 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_469388 : Nat := 118140960795 + 469388 * 2 ^ 59
def prefixEnd_469388 : Nat := 4983230072969 + 3 ^ 40 * 469388 * 2
def baseEnd_469388 : Nat := 107120736645651000440591

theorem tailTrace_469388 : CollatzResearch.WordTrace tailWord_469388 prefixEnd_469388 107120736645651000440591 := by
  unfold tailWord_469388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559993411747457966620409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11413324548996610622160545 8559993411747457966620409)
  ·
    refine ⟨6419995058810593474965307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8559993411747457966620409 6419995058810593474965307)
    ·
      refine ⟨9629992588215890212447961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6419995058810593474965307 9629992588215890212447961)
      ·
        refine ⟨7222494441161917659335971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9629992588215890212447961 7222494441161917659335971)
        ·
          refine ⟨10833741661742876489003957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222494441161917659335971 10833741661742876489003957)
          ·
            refine ⟨1015663280788394670844121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10833741661742876489003957 1015663280788394670844121)
            ·
              refine ⟨761747460591296003133091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015663280788394670844121 761747460591296003133091)
              ·
                refine ⟨1142621190886944004699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761747460591296003133091 1142621190886944004699637)
                ·
                  refine ⟨107120736645651000440591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142621190886944004699637 107120736645651000440591)
                  ·
                    rfl

theorem cell21_469388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_469388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469388 prefixEnd_469388 := by exact prefixLift 469388
  have htrace : WordTrace (prefixWord ++ tailWord_469388) baseStart_469388 baseEnd_469388 := by
    simpa [prefixWord, tailWord_469388, baseEnd_469388] using wordTrace_append hprefix tailTrace_469388
  have hstable : (prefixWord ++ tailWord_469388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469388).length < 2 ^ (prefixWord ++ tailWord_469388).sum := by decide
  have hdescent : baseEnd_469388 < baseStart_469388 := by decide
  rcases family_descends (prefixWord ++ tailWord_469388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469433 : List Nat := [1, 2, 1, 4, 3, 3, 7]
def baseStart_469433 : Nat := 118140960795 + 469433 * 2 ^ 59
def prefixEnd_469433 : Nat := 4983230072969 + 3 ^ 40 * 469433 * 2
def baseEnd_469433 : Nat := 11903445139860102465611

theorem tailTrace_469433 : CollatzResearch.WordTrace tailWord_469433 prefixEnd_469433 11903445139860102465611 := by
  unfold tailWord_469433
  simp only [CollatzResearch.WordTrace]
  refine ⟨17121628108331888618628953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11414418738887925745752635 17121628108331888618628953)
  ·
    refine ⟨12841221081248916463971715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17121628108331888618628953 12841221081248916463971715)
    ·
      refine ⟨19261831621873374695957573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841221081248916463971715 19261831621873374695957573)
      ·
        refine ⟨3611593429101257755492045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19261831621873374695957573 3611593429101257755492045)
        ·
          refine ⟨1354347535912971658309517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3611593429101257755492045 1354347535912971658309517)
          ·
            refine ⟨507880325967364371866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1354347535912971658309517 507880325967364371866069)
            ·
              refine ⟨11903445139860102465611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507880325967364371866069 11903445139860102465611)
              ·
                rfl

theorem cell21_469433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 7].length) (baseStart_469433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469433 prefixEnd_469433 := by exact prefixLift 469433
  have htrace : WordTrace (prefixWord ++ tailWord_469433) baseStart_469433 baseEnd_469433 := by
    simpa [prefixWord, tailWord_469433, baseEnd_469433] using wordTrace_append hprefix tailTrace_469433
  have hstable : (prefixWord ++ tailWord_469433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469433).length < 2 ^ (prefixWord ++ tailWord_469433).sum := by decide
  have hdescent : baseEnd_469433 < baseStart_469433 := by decide
  rcases family_descends (prefixWord ++ tailWord_469433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469523 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_469523 : Nat := 118140960795 + 469523 * 2 ^ 59
def prefixEnd_469523 : Nat := 4983230072969 + 3 ^ 40 * 469523 * 2
def baseEnd_469523 : Nat := 107151545484920765690315

theorem tailTrace_469523 : CollatzResearch.WordTrace tailWord_469523 prefixEnd_469523 107151545484920765690315 := by
  unfold tailWord_469523
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124910678005833989405223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11416607118670555992936815 17124910678005833989405223)
  ·
    refine ⟨25687366017008750984107835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17124910678005833989405223 25687366017008750984107835)
    ·
      refine ⟨38531049025513126476161753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687366017008750984107835 38531049025513126476161753)
      ·
        refine ⟨28898286769134844857121315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38531049025513126476161753 28898286769134844857121315)
        ·
          refine ⟨43347430153702267285681973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28898286769134844857121315 43347430153702267285681973)
          ·
            refine ⟨4063821576909587558032685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43347430153702267285681973 4063821576909587558032685)
            ·
              refine ⟨1523933091341095334262257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4063821576909587558032685 1523933091341095334262257)
              ·
                refine ⟨1142949818505821500696693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523933091341095334262257 1142949818505821500696693)
                ·
                  refine ⟨107151545484920765690315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142949818505821500696693 107151545484920765690315)
                  ·
                    rfl

theorem cell21_469523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_469523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469523 prefixEnd_469523 := by exact prefixLift 469523
  have htrace : WordTrace (prefixWord ++ tailWord_469523) baseStart_469523 baseEnd_469523 := by
    simpa [prefixWord, tailWord_469523, baseEnd_469523] using wordTrace_append hprefix tailTrace_469523
  have hstable : (prefixWord ++ tailWord_469523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469523).length < 2 ^ (prefixWord ++ tailWord_469523).sum := by decide
  have hdescent : baseEnd_469523 < baseStart_469523 := by decide
  rcases family_descends (prefixWord ++ tailWord_469523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469585 : List Nat := [1, 2, 2, 1, 3, 3, 4, 5]
def baseStart_469585 : Nat := 118140960795 + 469585 * 2 ^ 59
def prefixEnd_469585 : Nat := 4983230072969 + 3 ^ 40 * 469585 * 2
def baseEnd_469585 : Nat := 35721898243207478552285

theorem tailTrace_469585 : CollatzResearch.WordTrace tailWord_469585 prefixEnd_469585 35721898243207478552285 := by
  unfold tailWord_469585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127172003781218578162209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418114669187479052108139 17127172003781218578162209)
  ·
    refine ⟨12845379002835913933621657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17127172003781218578162209 12845379002835913933621657)
    ·
      refine ⟨9634034252126935450216243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12845379002835913933621657 9634034252126935450216243)
      ·
        refine ⟨14451051378190403175324365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634034252126935450216243 14451051378190403175324365)
        ·
          refine ⟨5419144266821401190746637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14451051378190403175324365 5419144266821401190746637)
          ·
            refine ⟨2032179100058025446529989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5419144266821401190746637 2032179100058025446529989)
            ·
              refine ⟨381033581260879771224373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2032179100058025446529989 381033581260879771224373)
              ·
                refine ⟨35721898243207478552285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381033581260879771224373 35721898243207478552285)
                ·
                  rfl

theorem cell21_469585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].length) (baseStart_469585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469585 prefixEnd_469585 := by exact prefixLift 469585
  have htrace : WordTrace (prefixWord ++ tailWord_469585) baseStart_469585 baseEnd_469585 := by
    simpa [prefixWord, tailWord_469585, baseEnd_469585] using wordTrace_append hprefix tailTrace_469585
  have hstable : (prefixWord ++ tailWord_469585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469585).length < 2 ^ (prefixWord ++ tailWord_469585).sum := by decide
  have hdescent : baseEnd_469585 < baseStart_469585 := by decide
  rcases family_descends (prefixWord ++ tailWord_469585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469622 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_469622 : Nat := 118140960795 + 469622 * 2 ^ 59
def prefixEnd_469622 : Nat := 4983230072969 + 3 ^ 40 * 469622 * 2
def baseEnd_469622 : Nat := 107174138633718593540113

theorem tailTrace_469622 : CollatzResearch.WordTrace tailWord_469622 prefixEnd_469622 107174138633718593540113 := by
  unfold tailWord_469622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070532594040448368578695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11419014336431449264839413 1070532594040448368578695)
  ·
    refine ⟨1605798891060672552868043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070532594040448368578695 1605798891060672552868043)
    ·
      refine ⟨2408698336591008829302065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605798891060672552868043 2408698336591008829302065)
      ·
        refine ⟨1806523752443256621976549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408698336591008829302065 1806523752443256621976549)
        ·
          refine ⟨338723203583110616620603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1806523752443256621976549 338723203583110616620603)
          ·
            refine ⟨508084805374665924930905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338723203583110616620603 508084805374665924930905)
            ·
              refine ⟨381063604030999443698179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508084805374665924930905 381063604030999443698179)
              ·
                refine ⟨571595406046499165547269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381063604030999443698179 571595406046499165547269)
                ·
                  refine ⟨107174138633718593540113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571595406046499165547269 107174138633718593540113)
                  ·
                    rfl

theorem cell21_469622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_469622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469622 prefixEnd_469622 := by exact prefixLift 469622
  have htrace : WordTrace (prefixWord ++ tailWord_469622) baseStart_469622 baseEnd_469622 := by
    simpa [prefixWord, tailWord_469622, baseEnd_469622] using wordTrace_append hprefix tailTrace_469622
  have hstable : (prefixWord ++ tailWord_469622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469622).length < 2 ^ (prefixWord ++ tailWord_469622).sum := by decide
  have hdescent : baseEnd_469622 < baseStart_469622 := by decide
  rcases family_descends (prefixWord ++ tailWord_469622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469678 : List Nat := [4, 1, 4, 1, 1, 1, 3, 6]
def baseStart_469678 : Nat := 118140960795 + 469678 * 2 ^ 59
def prefixEnd_469678 : Nat := 4983230072969 + 3 ^ 40 * 469678 * 2
def baseEnd_469678 : Nat := 35728972865558313535555

theorem tailTrace_469678 : CollatzResearch.WordTrace tailWord_469678 prefixEnd_469678 35728972865558313535555 := by
  unfold tailWord_469678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141320499055536932662211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11420375994962863640865125 2141320499055536932662211)
  ·
    refine ⟨3211980748583305398993317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141320499055536932662211 3211980748583305398993317)
    ·
      refine ⟨602246390359369762311247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3211980748583305398993317 602246390359369762311247)
      ·
        refine ⟨903369585539054643466871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602246390359369762311247 903369585539054643466871)
        ·
          refine ⟨1355054378308581965200307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903369585539054643466871 1355054378308581965200307)
          ·
            refine ⟨2032581567462872947800461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355054378308581965200307 2032581567462872947800461)
            ·
              refine ⟨762218087798577355425173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2032581567462872947800461 762218087798577355425173)
              ·
                refine ⟨35728972865558313535555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 762218087798577355425173 35728972865558313535555)
                ·
                  rfl

theorem cell21_469678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_469678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469678 prefixEnd_469678 := by exact prefixLift 469678
  have htrace : WordTrace (prefixWord ++ tailWord_469678) baseStart_469678 baseEnd_469678 := by
    simpa [prefixWord, tailWord_469678, baseEnd_469678] using wordTrace_append hprefix tailTrace_469678
  have hstable : (prefixWord ++ tailWord_469678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469678).length < 2 ^ (prefixWord ++ tailWord_469678).sum := by decide
  have hdescent : baseEnd_469678 < baseStart_469678 := by decide
  rcases family_descends (prefixWord ++ tailWord_469678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469689 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_469689 : Nat := 118140960795 + 469689 * 2 ^ 59
def prefixEnd_469689 : Nat := 4983230072969 + 3 ^ 40 * 469689 * 2
def baseEnd_469689 : Nat := 107189428946541365923309

theorem tailTrace_469689 : CollatzResearch.WordTrace tailWord_469689 prefixEnd_469689 107189428946541365923309 := by
  unfold tailWord_469689
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130965195404444339948121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11420643463602962893298747 17130965195404444339948121)
  ·
    refine ⟨12848223896553333254961091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17130965195404444339948121 12848223896553333254961091)
    ·
      refine ⟨19272335844829999882441637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848223896553333254961091 19272335844829999882441637)
      ·
        refine ⟨3613562970905624977957807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19272335844829999882441637 3613562970905624977957807)
        ·
          refine ⟨5420344456358437466936711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613562970905624977957807 5420344456358437466936711)
          ·
            refine ⟨8130516684537656200405067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420344456358437466936711 8130516684537656200405067)
            ·
              refine ⟨12195775026806484300607601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130516684537656200405067 12195775026806484300607601)
              ·
                refine ⟨9146831270104863225455701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12195775026806484300607601 9146831270104863225455701)
                ·
                  refine ⟨107189428946541365923309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9146831270104863225455701 107189428946541365923309)
                  ·
                    rfl

theorem cell21_469689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_469689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469689 prefixEnd_469689 := by exact prefixLift 469689
  have htrace : WordTrace (prefixWord ++ tailWord_469689) baseStart_469689 baseEnd_469689 := by
    simpa [prefixWord, tailWord_469689, baseEnd_469689] using wordTrace_append hprefix tailTrace_469689
  have hstable : (prefixWord ++ tailWord_469689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469689).length < 2 ^ (prefixWord ++ tailWord_469689).sum := by decide
  have hdescent : baseEnd_469689 < baseStart_469689 := by decide
  rcases family_descends (prefixWord ++ tailWord_469689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469720 : List Nat := [2, 1, 2, 2, 3, 3, 8]
def baseStart_469720 : Nat := 118140960795 + 469720 * 2 ^ 59
def prefixEnd_469720 : Nat := 4983230072969 + 3 ^ 40 * 469720 * 2
def baseEnd_469720 : Nat := 11910722618765800100731

theorem tailTrace_469720 : CollatzResearch.WordTrace tailWord_469720 prefixEnd_469720 11910722618765800100731 := by
  unfold tailWord_469720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566047929146068317163307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11421397238861424422884409 8566047929146068317163307)
  ·
    refine ⟨12849071893719102475744961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8566047929146068317163307 12849071893719102475744961)
    ·
      refine ⟨9636803920289326856808721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12849071893719102475744961 9636803920289326856808721)
      ·
        refine ⟨7227602940216995142606541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9636803920289326856808721 7227602940216995142606541)
        ·
          refine ⟨2710351102581373178477453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7227602940216995142606541 2710351102581373178477453)
          ·
            refine ⟨1016381663468014941929045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2710351102581373178477453 1016381663468014941929045)
            ·
              refine ⟨11910722618765800100731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1016381663468014941929045 11910722618765800100731)
              ·
                rfl

theorem cell21_469720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 8].length) (baseStart_469720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469720 prefixEnd_469720 := by exact prefixLift 469720
  have htrace : WordTrace (prefixWord ++ tailWord_469720) baseStart_469720 baseEnd_469720 := by
    simpa [prefixWord, tailWord_469720, baseEnd_469720] using wordTrace_append hprefix tailTrace_469720
  have hstable : (prefixWord ++ tailWord_469720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469720).length < 2 ^ (prefixWord ++ tailWord_469720).sum := by decide
  have hdescent : baseEnd_469720 < baseStart_469720 := by decide
  rcases family_descends (prefixWord ++ tailWord_469720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469830 : List Nat := [6, 1, 1, 2, 2, 9]
def baseStart_469830 : Nat := 118140960795 + 469830 * 2 ^ 59
def prefixEnd_469830 : Nat := 4983230072969 + 3 ^ 40 * 469830 * 2
def baseEnd_469830 : Nat := 3971170632131720521223

theorem tailTrace_469830 : CollatzResearch.WordTrace tailWord_469830 prefixEnd_469830 3971170632131720521223 := by
  unfold tailWord_469830
  simp only [CollatzResearch.WordTrace]
  refine ⟨535503371496675794400967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11424071925262416947220629 535503371496675794400967)
  ·
    refine ⟨803255057245013691601451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535503371496675794400967 803255057245013691601451)
    ·
      refine ⟨1204882585867520537402177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803255057245013691601451 1204882585867520537402177)
      ·
        refine ⟨903661939400640403051633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204882585867520537402177 903661939400640403051633)
        ·
          refine ⟨677746454550480302288725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903661939400640403051633 677746454550480302288725)
          ·
            refine ⟨3971170632131720521223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 677746454550480302288725 3971170632131720521223)
            ·
              rfl

theorem cell21_469830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 9].length) (baseStart_469830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469830 prefixEnd_469830 := by exact prefixLift 469830
  have htrace : WordTrace (prefixWord ++ tailWord_469830) baseStart_469830 baseEnd_469830 := by
    simpa [prefixWord, tailWord_469830, baseEnd_469830] using wordTrace_append hprefix tailTrace_469830
  have hstable : (prefixWord ++ tailWord_469830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469830).length < 2 ^ (prefixWord ++ tailWord_469830).sum := by decide
  have hdescent : baseEnd_469830 < baseStart_469830 := by decide
  rcases family_descends (prefixWord ++ tailWord_469830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469878 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_469878 : Nat := 118140960795 + 469878 * 2 ^ 59
def prefixEnd_469878 : Nat := 4983230072969 + 3 ^ 40 * 469878 * 2
def baseEnd_469878 : Nat := 107232561321519037272923

theorem tailTrace_469878 : CollatzResearch.WordTrace tailWord_469878 prefixEnd_469878 107232561321519037272923 := by
  unfold tailWord_469878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071116161982483101161143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11425239061146486412385525 1071116161982483101161143)
  ·
    refine ⟨1606674242973724651741715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1071116161982483101161143 1606674242973724651741715)
    ·
      refine ⟨2410011364460586977612573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606674242973724651741715 2410011364460586977612573)
      ·
        refine ⟨903754261672720116604715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2410011364460586977612573 903754261672720116604715)
        ·
          refine ⟨1355631392509080174907073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903754261672720116604715 1355631392509080174907073)
          ·
            refine ⟨1016723544381810131180305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355631392509080174907073 1016723544381810131180305)
            ·
              refine ⟨762542658286357598385229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016723544381810131180305 762542658286357598385229)
              ·
                refine ⟨285953496857384099394461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762542658286357598385229 285953496857384099394461)
                ·
                  refine ⟨107232561321519037272923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285953496857384099394461 107232561321519037272923)
                  ·
                    rfl

theorem cell21_469878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_469878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469878 prefixEnd_469878 := by exact prefixLift 469878
  have htrace : WordTrace (prefixWord ++ tailWord_469878) baseStart_469878 baseEnd_469878 := by
    simpa [prefixWord, tailWord_469878, baseEnd_469878] using wordTrace_append hprefix tailTrace_469878
  have hstable : (prefixWord ++ tailWord_469878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469878).length < 2 ^ (prefixWord ++ tailWord_469878).sum := by decide
  have hdescent : baseEnd_469878 < baseStart_469878 := by decide
  rcases family_descends (prefixWord ++ tailWord_469878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469931 : List Nat := [1, 1, 1, 1, 2, 1, 1, 13]
def baseStart_469931 : Nat := 118140960795 + 469931 * 2 ^ 59
def prefixEnd_469931 : Nat := 4983230072969 + 3 ^ 40 * 469931 * 2
def baseEnd_469931 : Nat := 35748218881200907629827

theorem tailTrace_469931 : CollatzResearch.WordTrace tailWord_469931 prefixEnd_469931 35748218881200907629827 := by
  unfold tailWord_469931
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139791660527719670257647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11426527773685146446838431 17139791660527719670257647)
  ·
    refine ⟨25709687490791579505386471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17139791660527719670257647 25709687490791579505386471)
    ·
      refine ⟨38564531236187369258079707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25709687490791579505386471 38564531236187369258079707)
      ·
        refine ⟨57846796854281053887119561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38564531236187369258079707 57846796854281053887119561)
        ·
          refine ⟨43385097640710790415339671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57846796854281053887119561 43385097640710790415339671)
          ·
            refine ⟨65077646461066185623009507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43385097640710790415339671 65077646461066185623009507)
            ·
              refine ⟨97616469691599278434514261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65077646461066185623009507 97616469691599278434514261)
              ·
                refine ⟨35748218881200907629827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 97616469691599278434514261 35748218881200907629827)
                ·
                  rfl

theorem cell21_469931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_469931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_469931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_469931 prefixEnd_469931 := by exact prefixLift 469931
  have htrace : WordTrace (prefixWord ++ tailWord_469931) baseStart_469931 baseEnd_469931 := by
    simpa [prefixWord, tailWord_469931, baseEnd_469931] using wordTrace_append hprefix tailTrace_469931
  have hstable : (prefixWord ++ tailWord_469931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469931).length < 2 ^ (prefixWord ++ tailWord_469931).sum := by decide
  have hdescent : baseEnd_469931 < baseStart_469931 := by decide
  rcases family_descends (prefixWord ++ tailWord_469931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470024 : List Nat := [2, 1, 3, 2, 1, 3, 3, 6]
def baseStart_470024 : Nat := 118140960795 + 470024 * 2 ^ 59
def prefixEnd_470024 : Nat := 4983230072969 + 3 ^ 40 * 470024 * 2
def baseEnd_470024 : Nat := 35755293503551742613097

theorem tailTrace_470024 : CollatzResearch.WordTrace tailWord_470024 prefixEnd_470024 35755293503551742613097 := by
  unfold tailWord_470024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571591824595398276696563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11428789099460531035595417 8571591824595398276696563)
  ·
    refine ⟨12857387736893097415044845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8571591824595398276696563 12857387736893097415044845)
    ·
      refine ⟨4821520401334911530641817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12857387736893097415044845 4821520401334911530641817)
      ·
        refine ⟨3616140301001183647981363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4821520401334911530641817 3616140301001183647981363)
        ·
          refine ⟨5424210451501775471972045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616140301001183647981363 5424210451501775471972045)
          ·
            refine ⟨2034078919313165801989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5424210451501775471972045 2034078919313165801989517)
            ·
              refine ⟨762779594742437175746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2034078919313165801989517 762779594742437175746069)
              ·
                refine ⟨35755293503551742613097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 762779594742437175746069 35755293503551742613097)
                ·
                  rfl

theorem cell21_470024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_470024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470024 prefixEnd_470024 := by exact prefixLift 470024
  have htrace : WordTrace (prefixWord ++ tailWord_470024) baseStart_470024 baseEnd_470024 := by
    simpa [prefixWord, tailWord_470024, baseEnd_470024] using wordTrace_append hprefix tailTrace_470024
  have hstable : (prefixWord ++ tailWord_470024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470024).length < 2 ^ (prefixWord ++ tailWord_470024).sum := by decide
  have hdescent : baseEnd_470024 < baseStart_470024 := by decide
  rcases family_descends (prefixWord ++ tailWord_470024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470072 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_470072 : Nat := 118140960795 + 470072 * 2 ^ 59
def prefixEnd_470072 : Nat := 4983230072969 + 3 ^ 40 * 470072 * 2
def baseEnd_470072 : Nat := 107276834764617811039193

theorem tailTrace_470072 : CollatzResearch.WordTrace tailWord_470072 prefixEnd_470072 107276834764617811039193 := by
  unfold tailWord_470072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572467176508450375570235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11429956235344600500760313 8572467176508450375570235)
  ·
    refine ⟨12858700764762675563355353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8572467176508450375570235 12858700764762675563355353)
    ·
      refine ⟨9644025573572006672516515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12858700764762675563355353 9644025573572006672516515)
      ·
        refine ⟨14466038360358010008774773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644025573572006672516515 14466038360358010008774773)
        ·
          refine ⟨1356191096283563438322635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14466038360358010008774773 1356191096283563438322635)
          ·
            refine ⟨2034286644425345157483953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356191096283563438322635 2034286644425345157483953)
            ·
              refine ⟨1525714983319008868112965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034286644425345157483953 1525714983319008868112965)
              ·
                refine ⟨286071559372314162771181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1525714983319008868112965 286071559372314162771181)
                ·
                  refine ⟨107276834764617811039193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286071559372314162771181 107276834764617811039193)
                  ·
                    rfl

theorem cell21_470072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_470072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470072 prefixEnd_470072 := by exact prefixLift 470072
  have htrace : WordTrace (prefixWord ++ tailWord_470072) baseStart_470072 baseEnd_470072 := by
    simpa [prefixWord, tailWord_470072, baseEnd_470072] using wordTrace_append hprefix tailTrace_470072
  have hstable : (prefixWord ++ tailWord_470072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470072).length < 2 ^ (prefixWord ++ tailWord_470072).sum := by decide
  have hdescent : baseEnd_470072 < baseStart_470072 := by decide
  rcases family_descends (prefixWord ++ tailWord_470072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470083 : List Nat := [1, 1, 1, 3, 1, 2, 4, 8]
def baseStart_470083 : Nat := 118140960795 + 470083 * 2 ^ 59
def prefixEnd_470083 : Nat := 4983230072969 + 3 ^ 40 * 470083 * 2
def baseEnd_470083 : Nat := 35759781704828078785279

theorem tailTrace_470083 : CollatzResearch.WordTrace tailWord_470083 prefixEnd_470083 35759781704828078785279 := by
  unfold tailWord_470083
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145335555977049629790903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11430223703984699753193935 17145335555977049629790903)
  ·
    refine ⟨25718003333965574444686355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17145335555977049629790903 25718003333965574444686355)
    ·
      refine ⟨38577005000948361667029533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25718003333965574444686355 38577005000948361667029533)
      ·
        refine ⟨14466376875355635625136075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38577005000948361667029533 14466376875355635625136075)
        ·
          refine ⟨21699565313033453437704113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466376875355635625136075 21699565313033453437704113)
          ·
            refine ⟨16274673984775090078278085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21699565313033453437704113 16274673984775090078278085)
            ·
              refine ⟨3051501372145329389677141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16274673984775090078278085 3051501372145329389677141)
              ·
                refine ⟨35759781704828078785279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3051501372145329389677141 35759781704828078785279)
                ·
                  rfl

theorem cell21_470083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_470083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470083 prefixEnd_470083 := by exact prefixLift 470083
  have htrace : WordTrace (prefixWord ++ tailWord_470083) baseStart_470083 baseEnd_470083 := by
    simpa [prefixWord, tailWord_470083, baseEnd_470083] using wordTrace_append hprefix tailTrace_470083
  have hstable : (prefixWord ++ tailWord_470083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470083).length < 2 ^ (prefixWord ++ tailWord_470083).sum := by decide
  have hdescent : baseEnd_470083 < baseStart_470083 := by decide
  rcases family_descends (prefixWord ++ tailWord_470083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470193 : List Nat := [1, 2, 2, 5, 1, 3, 1, 6]
def baseStart_470193 : Nat := 118140960795 + 470193 * 2 ^ 59
def prefixEnd_470193 : Nat := 4983230072969 + 3 ^ 40 * 470193 * 2
def baseEnd_470193 : Nat := 35768149537716163174093

theorem tailTrace_470193 : CollatzResearch.WordTrace tailWord_470193 prefixEnd_470193 35768149537716163174093 := by
  unfold tailWord_470193
  simp only [CollatzResearch.WordTrace]
  refine ⟨17149347585578538416295233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11432898390385692277530155 17149347585578538416295233)
  ·
    refine ⟨12862010689183903812221425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17149347585578538416295233 12862010689183903812221425)
    ·
      refine ⟨9646508016887927859166069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12862010689183903812221425 9646508016887927859166069)
      ·
        refine ⟨904360126583243236796819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9646508016887927859166069 904360126583243236796819)
        ·
          refine ⟨1356540189874864855195229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904360126583243236796819 1356540189874864855195229)
          ·
            refine ⟨508702571203074320698211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1356540189874864855195229 508702571203074320698211)
            ·
              refine ⟨763053856804611481047317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508702571203074320698211 763053856804611481047317)
              ·
                refine ⟨35768149537716163174093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763053856804611481047317 35768149537716163174093)
                ·
                  rfl

theorem cell21_470193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_470193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470193 prefixEnd_470193 := by exact prefixLift 470193
  have htrace : WordTrace (prefixWord ++ tailWord_470193) baseStart_470193 baseEnd_470193 := by
    simpa [prefixWord, tailWord_470193, baseEnd_470193] using wordTrace_append hprefix tailTrace_470193
  have hstable : (prefixWord ++ tailWord_470193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470193).length < 2 ^ (prefixWord ++ tailWord_470193).sum := by decide
  have hdescent : baseEnd_470193 < baseStart_470193 := by decide
  rcases family_descends (prefixWord ++ tailWord_470193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470255 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 4]
def baseStart_470255 : Nat := 118140960795 + 470255 * 2 ^ 59
def prefixEnd_470255 : Nat := 4983230072969 + 3 ^ 40 * 470255 * 2
def baseEnd_470255 : Nat := 107318597857850159488819

theorem tailTrace_470255 : CollatzResearch.WordTrace tailWord_470255 prefixEnd_470255 107318597857850159488819 := by
  unfold tailWord_470255
  simp only [CollatzResearch.WordTrace]
  refine ⟨17151608911353923005052219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11434405940902615336701479 17151608911353923005052219)
  ·
    refine ⟨25727413367030884507578329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17151608911353923005052219 25727413367030884507578329)
    ·
      refine ⟨19295560025273163380683747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25727413367030884507578329 19295560025273163380683747)
      ·
        refine ⟨28943340037909745071025621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19295560025273163380683747 28943340037909745071025621)
        ·
          refine ⟨678359532138509650102163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28943340037909745071025621 678359532138509650102163)
          ·
            refine ⟨1017539298207764475153245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678359532138509650102163 1017539298207764475153245)
            ·
              refine ⟨381577236827911678182467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1017539298207764475153245 381577236827911678182467)
              ·
                refine ⟨572365855241867517273701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381577236827911678182467 572365855241867517273701)
                ·
                  refine ⟨107318597857850159488819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572365855241867517273701 107318597857850159488819)
                  ·
                    rfl

theorem cell21_470255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_470255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470255 prefixEnd_470255 := by exact prefixLift 470255
  have htrace : WordTrace (prefixWord ++ tailWord_470255) baseStart_470255 baseEnd_470255 := by
    simpa [prefixWord, tailWord_470255, baseEnd_470255] using wordTrace_append hprefix tailTrace_470255
  have hstable : (prefixWord ++ tailWord_470255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470255).length < 2 ^ (prefixWord ++ tailWord_470255).sum := by decide
  have hdescent : baseEnd_470255 < baseStart_470255 := by decide
  rcases family_descends (prefixWord ++ tailWord_470255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470266 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_470266 : Nat := 118140960795 + 470266 * 2 ^ 59
def prefixEnd_470266 : Nat := 4983230072969 + 3 ^ 40 * 470266 * 2
def baseEnd_470266 : Nat := 107321108207716584805463

theorem tailTrace_470266 : CollatzResearch.WordTrace tailWord_470266 prefixEnd_470266 107321108207716584805463 := by
  unfold tailWord_470266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288002528578517970925663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11434673409542714589135101 4288002528578517970925663)
  ·
    refine ⟨6432003792867776956388495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288002528578517970925663 6432003792867776956388495)
    ·
      refine ⟨9648005689301665434582743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432003792867776956388495 9648005689301665434582743)
      ·
        refine ⟨14472008533952498151874115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9648005689301665434582743 14472008533952498151874115)
        ·
          refine ⟨21708012800928747227811173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14472008533952498151874115 21708012800928747227811173)
          ·
            refine ⟨4070252400174140105214595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21708012800928747227811173 4070252400174140105214595)
            ·
              refine ⟨6105378600261210157821893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070252400174140105214595 6105378600261210157821893)
              ·
                refine ⟨1144758487548976904591605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6105378600261210157821893 1144758487548976904591605)
                ·
                  refine ⟨107321108207716584805463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1144758487548976904591605 107321108207716584805463)
                  ·
                    rfl

theorem cell21_470266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_470266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470266 prefixEnd_470266 := by exact prefixLift 470266
  have htrace : WordTrace (prefixWord ++ tailWord_470266) baseStart_470266 baseEnd_470266 := by
    simpa [prefixWord, tailWord_470266, baseEnd_470266] using wordTrace_append hprefix tailTrace_470266
  have hstable : (prefixWord ++ tailWord_470266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470266).length < 2 ^ (prefixWord ++ tailWord_470266).sum := by decide
  have hdescent : baseEnd_470266 < baseStart_470266 := by decide
  rcases family_descends (prefixWord ++ tailWord_470266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470373 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_470373 : Nat := 118140960795 + 470373 * 2 ^ 59
def prefixEnd_470373 : Nat := 4983230072969 + 3 ^ 40 * 470373 * 2
def baseEnd_470373 : Nat := 107345527065508176521911

theorem tailTrace_470373 : CollatzResearch.WordTrace tailWord_470373 prefixEnd_470373 107345527065508176521911 := by
  unfold tailWord_470373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17155912724926429157847773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11437275149950952771898515 17155912724926429157847773)
  ·
    refine ⟨6433467271847410934192915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17155912724926429157847773 6433467271847410934192915)
    ·
      refine ⟨9650200907771116401289373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433467271847410934192915 9650200907771116401289373)
      ·
        refine ⟨3618825340414168650483515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9650200907771116401289373 3618825340414168650483515)
        ·
          refine ⟨5428238010621252975725273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618825340414168650483515 5428238010621252975725273)
          ·
            refine ⟨4071178507965939731793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428238010621252975725273 4071178507965939731793955)
            ·
              refine ⟨6106767761948909597690933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071178507965939731793955 6106767761948909597690933)
              ·
                refine ⟨572509477682710274783525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6106767761948909597690933 572509477682710274783525)
                ·
                  refine ⟨107345527065508176521911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572509477682710274783525 107345527065508176521911)
                  ·
                    rfl

theorem cell21_470373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_470373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470373 prefixEnd_470373 := by exact prefixLift 470373
  have htrace : WordTrace (prefixWord ++ tailWord_470373) baseStart_470373 baseEnd_470373 := by
    simpa [prefixWord, tailWord_470373, baseEnd_470373] using wordTrace_append hprefix tailTrace_470373
  have hstable : (prefixWord ++ tailWord_470373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470373).length < 2 ^ (prefixWord ++ tailWord_470373).sum := by decide
  have hdescent : baseEnd_470373 < baseStart_470373 := by decide
  rcases family_descends (prefixWord ++ tailWord_470373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470508 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_470508 : Nat := 118140960795 + 470508 * 2 ^ 59
def prefixEnd_470508 : Nat := 4983230072969 + 3 ^ 40 * 470508 * 2
def baseEnd_470508 : Nat := 107376335904777941771635

theorem tailTrace_470508 : CollatzResearch.WordTrace tailWord_470508 prefixEnd_470508 107376335904777941771635 := by
  unfold tailWord_470508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580418289718673607006089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11440557719624898142674785 8580418289718673607006089)
  ·
    refine ⟨6435313717289005205254567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8580418289718673607006089 6435313717289005205254567)
    ·
      refine ⟨9652970575933507807881851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435313717289005205254567 9652970575933507807881851)
      ·
        refine ⟨14479455863900261711822777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652970575933507807881851 14479455863900261711822777)
        ·
          refine ⟨10859591897925196283867083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14479455863900261711822777 10859591897925196283867083)
          ·
            refine ⟨16289387846887794425800625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10859591897925196283867083 16289387846887794425800625)
            ·
              refine ⟨12217040885165845819350469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16289387846887794425800625 12217040885165845819350469)
              ·
                refine ⟨2290695165968596091128213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12217040885165845819350469 2290695165968596091128213)
                ·
                  refine ⟨107376335904777941771635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2290695165968596091128213 107376335904777941771635)
                  ·
                    rfl

theorem cell21_470508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_470508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470508 prefixEnd_470508 := by exact prefixLift 470508
  have htrace : WordTrace (prefixWord ++ tailWord_470508) baseStart_470508 baseEnd_470508 := by
    simpa [prefixWord, tailWord_470508, baseEnd_470508] using wordTrace_append hprefix tailTrace_470508
  have hstable : (prefixWord ++ tailWord_470508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470508).length < 2 ^ (prefixWord ++ tailWord_470508).sum := by decide
  have hdescent : baseEnd_470508 < baseStart_470508 := by decide
  rcases family_descends (prefixWord ++ tailWord_470508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470525 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_470525 : Nat := 118140960795 + 470525 * 2 ^ 59
def prefixEnd_470525 : Nat := 4983230072969 + 3 ^ 40 * 470525 * 2
def baseEnd_470525 : Nat := 107380215536389689988267

theorem tailTrace_470525 : CollatzResearch.WordTrace tailWord_470525 prefixEnd_470525 107380215536389689988267 := by
  unfold tailWord_470525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161456620375759117381029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11440971080250506078254019 17161456620375759117381029)
  ·
    refine ⟨3217773116320454834508943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17161456620375759117381029 3217773116320454834508943)
    ·
      refine ⟨4826659674480682251763415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217773116320454834508943 4826659674480682251763415)
      ·
        refine ⟨7239989511721023377645123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826659674480682251763415 7239989511721023377645123)
        ·
          refine ⟨10859984267581535066467685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239989511721023377645123 10859984267581535066467685)
          ·
            refine ⟨2036247050171537824962691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10859984267581535066467685 2036247050171537824962691)
            ·
              refine ⟨3054370575257306737444037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036247050171537824962691 3054370575257306737444037)
              ·
                refine ⟨572694482860745013270757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3054370575257306737444037 572694482860745013270757)
                ·
                  refine ⟨107380215536389689988267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572694482860745013270757 107380215536389689988267)
                  ·
                    rfl

theorem cell21_470525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_470525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470525 prefixEnd_470525 := by exact prefixLift 470525
  have htrace : WordTrace (prefixWord ++ tailWord_470525) baseStart_470525 baseEnd_470525 := by
    simpa [prefixWord, tailWord_470525, baseEnd_470525] using wordTrace_append hprefix tailTrace_470525
  have hstable : (prefixWord ++ tailWord_470525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470525).length < 2 ^ (prefixWord ++ tailWord_470525).sum := by decide
  have hdescent : baseEnd_470525 < baseStart_470525 := by decide
  rcases family_descends (prefixWord ++ tailWord_470525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470556 : List Nat := [2, 2, 3, 1, 2, 1, 5, 5]
def baseStart_470556 : Nat := 118140960795 + 470556 * 2 ^ 59
def prefixEnd_470556 : Nat := 4983230072969 + 3 ^ 40 * 470556 * 2
def baseEnd_470556 : Nat := 35795763386246841657179

theorem tailTrace_470556 : CollatzResearch.WordTrace tailWord_470556 prefixEnd_470556 35795763386246841657179 := by
  unfold tailWord_470556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581293641631725705879761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11441724855508967607839681 8581293641631725705879761)
  ·
    refine ⟨6435970231223794279409821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8581293641631725705879761 6435970231223794279409821)
    ·
      refine ⟨2413488836708922854778683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6435970231223794279409821 2413488836708922854778683)
      ·
        refine ⟨3620233255063384282168025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413488836708922854778683 3620233255063384282168025)
        ·
          refine ⟨2715174941297538211626019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620233255063384282168025 2715174941297538211626019)
          ·
            refine ⟨4072762411946307317439029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715174941297538211626019 4072762411946307317439029)
            ·
              refine ⟨381821476119966311009909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4072762411946307317439029 381821476119966311009909)
              ·
                refine ⟨35795763386246841657179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381821476119966311009909 35795763386246841657179)
                ·
                  rfl

theorem cell21_470556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_470556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470556 prefixEnd_470556 := by exact prefixLift 470556
  have htrace : WordTrace (prefixWord ++ tailWord_470556) baseStart_470556 baseEnd_470556 := by
    simpa [prefixWord, tailWord_470556, baseEnd_470556] using wordTrace_append hprefix tailTrace_470556
  have hstable : (prefixWord ++ tailWord_470556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470556).length < 2 ^ (prefixWord ++ tailWord_470556).sum := by decide
  have hdescent : baseEnd_470556 < baseStart_470556 := by decide
  rcases family_descends (prefixWord ++ tailWord_470556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470570 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_470570 : Nat := 118140960795 + 470570 * 2 ^ 59
def prefixEnd_470570 : Nat := 4983230072969 + 3 ^ 40 * 470570 * 2
def baseEnd_470570 : Nat := 107390485149479611738175

theorem tailTrace_470570 : CollatzResearch.WordTrace tailWord_470570 prefixEnd_470570 107390485149479611738175 := by
  unfold tailWord_470570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290774476303182950692291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11442065270141821201846109 4290774476303182950692291)
  ·
    refine ⟨6436161714454774426038437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290774476303182950692291 6436161714454774426038437)
    ·
      refine ⟨1206780321460270204882207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6436161714454774426038437 1206780321460270204882207)
      ·
        refine ⟨1810170482190405307323311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206780321460270204882207 1810170482190405307323311)
        ·
          refine ⟨2715255723285607960984967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810170482190405307323311 2715255723285607960984967)
          ·
            refine ⟨4072883584928411941477451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715255723285607960984967 4072883584928411941477451)
            ·
              refine ⟨6109325377392617912216177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072883584928411941477451 6109325377392617912216177)
              ·
                refine ⟨4581994033044463434162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109325377392617912216177 4581994033044463434162133)
                ·
                  refine ⟨107390485149479611738175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4581994033044463434162133 107390485149479611738175)
                  ·
                    rfl

theorem cell21_470570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_470570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470570 prefixEnd_470570 := by exact prefixLift 470570
  have htrace : WordTrace (prefixWord ++ tailWord_470570) baseStart_470570 baseEnd_470570 := by
    simpa [prefixWord, tailWord_470570, baseEnd_470570] using wordTrace_append hprefix tailTrace_470570
  have hstable : (prefixWord ++ tailWord_470570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470570).length < 2 ^ (prefixWord ++ tailWord_470570).sum := by decide
  have hdescent : baseEnd_470570 < baseStart_470570 := by decide
  rcases family_descends (prefixWord ++ tailWord_470570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470615 : List Nat := [1, 1, 3, 2, 2, 4, 1, 7]
def baseStart_470615 : Nat := 118140960795 + 470615 * 2 ^ 59
def prefixEnd_470615 : Nat := 4983230072969 + 3 ^ 40 * 470615 * 2
def baseEnd_470615 : Nat := 35800251587523177829361

theorem tailTrace_470615 : CollatzResearch.WordTrace tailWord_470615 prefixEnd_470615 35800251587523177829361 := by
  unfold tailWord_470615
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164739190049704488157299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11443159460033136325438199 17164739190049704488157299)
  ·
    refine ⟨25747108785074556732235949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17164739190049704488157299 25747108785074556732235949)
    ·
      refine ⟨9655165794402958774588481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25747108785074556732235949 9655165794402958774588481)
      ·
        refine ⟨7241374345802219080941361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655165794402958774588481 7241374345802219080941361)
        ·
          refine ⟨5431030759351664310706021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7241374345802219080941361 5431030759351664310706021)
          ·
            refine ⟨1018318267378437058257379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5431030759351664310706021 1018318267378437058257379)
            ·
              refine ⟨1527477401067655587386069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018318267378437058257379 1527477401067655587386069)
              ·
                refine ⟨35800251587523177829361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1527477401067655587386069 35800251587523177829361)
                ·
                  rfl

theorem cell21_470615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_470615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470615 prefixEnd_470615 := by exact prefixLift 470615
  have htrace : WordTrace (prefixWord ++ tailWord_470615) baseStart_470615 baseEnd_470615 := by
    simpa [prefixWord, tailWord_470615, baseEnd_470615] using wordTrace_append hprefix tailTrace_470615
  have hstable : (prefixWord ++ tailWord_470615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470615).length < 2 ^ (prefixWord ++ tailWord_470615).sum := by decide
  have hdescent : baseEnd_470615 < baseStart_470615 := by decide
  rcases family_descends (prefixWord ++ tailWord_470615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470632 : List Nat := [2, 1, 4, 3, 1, 3, 7]
def baseStart_470632 : Nat := 118140960795 + 470632 * 2 ^ 59
def prefixEnd_470632 : Nat := 4983230072969 + 3 ^ 40 * 470632 * 2
def baseEnd_470632 : Nat := 11933848266020142411635

theorem tailTrace_470632 : CollatzResearch.WordTrace tailWord_470632 prefixEnd_470632 11933848266020142411635 := by
  unfold tailWord_470632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582679615494058195763075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11443572820658744261017433 8582679615494058195763075)
  ·
    refine ⟨12874019423241087293644613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582679615494058195763075 12874019423241087293644613)
    ·
      refine ⟨2413878641857703867558365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12874019423241087293644613 2413878641857703867558365)
      ·
        refine ⟨905204490696638950334387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2413878641857703867558365 905204490696638950334387)
        ·
          refine ⟨1357806736044958425501581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905204490696638950334387 1357806736044958425501581)
          ·
            refine ⟨509177526016859409563093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357806736044958425501581 509177526016859409563093)
            ·
              refine ⟨11933848266020142411635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 509177526016859409563093 11933848266020142411635)
              ·
                rfl

theorem cell21_470632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 7].length) (baseStart_470632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470632 prefixEnd_470632 := by exact prefixLift 470632
  have htrace : WordTrace (prefixWord ++ tailWord_470632) baseStart_470632 baseEnd_470632 := by
    simpa [prefixWord, tailWord_470632, baseEnd_470632] using wordTrace_append hprefix tailTrace_470632
  have hstable : (prefixWord ++ tailWord_470632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470632).length < 2 ^ (prefixWord ++ tailWord_470632).sum := by decide
  have hdescent : baseEnd_470632 < baseStart_470632 := by decide
  rcases family_descends (prefixWord ++ tailWord_470632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470753 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_470753 : Nat := 118140960795 + 470753 * 2 ^ 59
def prefixEnd_470753 : Nat := 4983230072969 + 3 ^ 40 * 470753 * 2
def baseEnd_470753 : Nat := 107432248242711960187801

theorem tailTrace_470753 : CollatzResearch.WordTrace tailWord_470753 prefixEnd_470753 107432248242711960187801 := by
  unfold tailWord_470753
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169772463549754056680913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11446514975699836037787275 17169772463549754056680913)
  ·
    refine ⟨12877329347662315542510685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17169772463549754056680913 12877329347662315542510685)
    ·
      refine ⟨4828998505373368328441507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12877329347662315542510685 4828998505373368328441507)
      ·
        refine ⟨7243497758060052492662261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828998505373368328441507 7243497758060052492662261)
        ·
          refine ⟨679077914818129921187087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7243497758060052492662261 679077914818129921187087)
          ·
            refine ⟨1018616872227194881780631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679077914818129921187087 1018616872227194881780631)
            ·
              refine ⟨1527925308340792322670947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018616872227194881780631 1527925308340792322670947)
              ·
                refine ⟨2291887962511188484006421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527925308340792322670947 2291887962511188484006421)
                ·
                  refine ⟨107432248242711960187801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2291887962511188484006421 107432248242711960187801)
                  ·
                    rfl

theorem cell21_470753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_470753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470753 prefixEnd_470753 := by exact prefixLift 470753
  have htrace : WordTrace (prefixWord ++ tailWord_470753) baseStart_470753 baseEnd_470753 := by
    simpa [prefixWord, tailWord_470753, baseEnd_470753] using wordTrace_append hprefix tailTrace_470753
  have hstable : (prefixWord ++ tailWord_470753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470753).length < 2 ^ (prefixWord ++ tailWord_470753).sum := by decide
  have hdescent : baseEnd_470753 < baseStart_470753 := by decide
  rcases family_descends (prefixWord ++ tailWord_470753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470770 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_470770 : Nat := 118140960795 + 470770 * 2 ^ 59
def prefixEnd_470770 : Nat := 4983230072969 + 3 ^ 40 * 470770 * 2
def baseEnd_470770 : Nat := 107436127874323708404433

theorem tailTrace_470770 : CollatzResearch.WordTrace tailWord_470770 prefixEnd_470770 107436127874323708404433 := by
  unfold tailWord_470770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292598126122041490012441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11446928336325443973366509 4292598126122041490012441)
  ·
    refine ⟨3219448594591531117509331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4292598126122041490012441 3219448594591531117509331)
    ·
      refine ⟨4829172891887296676263997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219448594591531117509331 4829172891887296676263997)
      ·
        refine ⟨1810939834457736253598999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4829172891887296676263997 1810939834457736253598999)
        ·
          refine ⟨2716409751686604380398499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810939834457736253598999 2716409751686604380398499)
          ·
            refine ⟨4074614627529906570597749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716409751686604380398499 4074614627529906570597749)
            ·
              refine ⟨381995121330928740993539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4074614627529906570597749 381995121330928740993539)
              ·
                refine ⟨572992681996393111490309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381995121330928740993539 572992681996393111490309)
                ·
                  refine ⟨107436127874323708404433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572992681996393111490309 107436127874323708404433)
                  ·
                    rfl

theorem cell21_470770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_470770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470770 prefixEnd_470770 := by exact prefixLift 470770
  have htrace : WordTrace (prefixWord ++ tailWord_470770) baseStart_470770 baseEnd_470770 := by
    simpa [prefixWord, tailWord_470770, baseEnd_470770] using wordTrace_append hprefix tailTrace_470770
  have hstable : (prefixWord ++ tailWord_470770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470770).length < 2 ^ (prefixWord ++ tailWord_470770).sum := by decide
  have hdescent : baseEnd_470770 < baseStart_470770 := by decide
  rcases family_descends (prefixWord ++ tailWord_470770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470781 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_470781 : Nat := 118140960795 + 470781 * 2 ^ 59
def prefixEnd_470781 : Nat := 4983230072969 + 3 ^ 40 * 470781 * 2
def baseEnd_470781 : Nat := 107438638224190133721077

theorem tailTrace_470781 : CollatzResearch.WordTrace tailWord_470781 prefixEnd_470781 107438638224190133721077 := by
  unfold tailWord_470781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170793707448314838700197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447195804965543225800131 17170793707448314838700197)
  ·
    refine ⟨3219523820146559032256287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17170793707448314838700197 3219523820146559032256287)
    ·
      refine ⟨4829285730219838548384431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219523820146559032256287 4829285730219838548384431)
      ·
        refine ⟨7243928595329757822576647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829285730219838548384431 7243928595329757822576647)
        ·
          refine ⟨10865892892994636733864971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243928595329757822576647 10865892892994636733864971)
          ·
            refine ⟨16298839339491955100797457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10865892892994636733864971 16298839339491955100797457)
            ·
              refine ⟨12224129504618966325598093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16298839339491955100797457 12224129504618966325598093)
              ·
                refine ⟨4584048564232112372099285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12224129504618966325598093 4584048564232112372099285)
                ·
                  refine ⟨107438638224190133721077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4584048564232112372099285 107438638224190133721077)
                  ·
                    rfl

theorem cell21_470781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_470781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470781 prefixEnd_470781 := by exact prefixLift 470781
  have htrace : WordTrace (prefixWord ++ tailWord_470781) baseStart_470781 baseEnd_470781 := by
    simpa [prefixWord, tailWord_470781, baseEnd_470781] using wordTrace_append hprefix tailTrace_470781
  have hstable : (prefixWord ++ tailWord_470781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470781).length < 2 ^ (prefixWord ++ tailWord_470781).sum := by decide
  have hdescent : baseEnd_470781 < baseStart_470781 := by decide
  rcases family_descends (prefixWord ++ tailWord_470781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470812 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_470812 : Nat := 118140960795 + 470812 * 2 ^ 59
def prefixEnd_470812 : Nat := 4983230072969 + 3 ^ 40 * 470812 * 2
def baseEnd_470812 : Nat := 107445712846540968704347

theorem tailTrace_470812 : CollatzResearch.WordTrace tailWord_470812 prefixEnd_470812 107445712846540968704347 := by
  unfold tailWord_470812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585962185168003566539345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11447949580224004755385793 8585962185168003566539345)
  ·
    refine ⟨6439471638876002674904509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8585962185168003566539345 6439471638876002674904509)
    ·
      refine ⟨2414801864578501003089191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6439471638876002674904509 2414801864578501003089191)
      ·
        refine ⟨3622202796867751504633787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414801864578501003089191 3622202796867751504633787)
        ·
          refine ⟨5433304195301627256950681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622202796867751504633787 5433304195301627256950681)
          ·
            refine ⟨4074978146476220442713011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433304195301627256950681 4074978146476220442713011)
            ·
              refine ⟨6112467219714330664069517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074978146476220442713011 6112467219714330664069517)
              ·
                refine ⟨2292175207392873999026069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6112467219714330664069517 2292175207392873999026069)
                ·
                  refine ⟨107445712846540968704347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2292175207392873999026069 107445712846540968704347)
                  ·
                    rfl

theorem cell21_470812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_470812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470812 prefixEnd_470812 := by exact prefixLift 470812
  have htrace : WordTrace (prefixWord ++ tailWord_470812) baseStart_470812 baseEnd_470812 := by
    simpa [prefixWord, tailWord_470812, baseEnd_470812] using wordTrace_append hprefix tailTrace_470812
  have hstable : (prefixWord ++ tailWord_470812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470812).length < 2 ^ (prefixWord ++ tailWord_470812).sum := by decide
  have hdescent : baseEnd_470812 < baseStart_470812 := by decide
  rcases family_descends (prefixWord ++ tailWord_470812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
