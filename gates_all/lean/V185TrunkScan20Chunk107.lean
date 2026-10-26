import V185TrunkScan20Chunk106

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_649860 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_649860 : Nat := 118140960795 + 649860 * 2 ^ 59
def prefixEnd_649860 : Nat := 4983230072969 + 3 ^ 40 * 649860 * 2
def baseEnd_649860 : Nat := 296613811671940136410093

theorem tailTrace_649860 : CollatzResearch.WordTrace tailWord_649860 prefixEnd_649860 296613811671940136410093 := by
  unfold tailWord_649860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851170712837841048481517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15801560950450454731308689 11851170712837841048481517)
  ·
    refine ⟨4444189017314190393180569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11851170712837841048481517 4444189017314190393180569)
    ·
      refine ⟨3333141762985642794885427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4444189017314190393180569 3333141762985642794885427)
      ·
        refine ⟨4999712644478464192328141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333141762985642794885427 4999712644478464192328141)
        ·
          refine ⟨1874892241679424072123053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4999712644478464192328141 1874892241679424072123053)
          ·
            refine ⟨703084590629784027046145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1874892241679424072123053 703084590629784027046145)
            ·
              refine ⟨527313442972338020284609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703084590629784027046145 527313442972338020284609)
              ·
                refine ⟨395485082229253515213457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527313442972338020284609 395485082229253515213457)
                ·
                  refine ⟨296613811671940136410093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395485082229253515213457 296613811671940136410093)
                  ·
                    rfl

theorem cell20_649860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_649860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649860 prefixEnd_649860 := by exact prefixLift 649860
  have htrace : WordTrace (prefixWord ++ tailWord_649860) baseStart_649860 baseEnd_649860 := by
    simpa [prefixWord, tailWord_649860, baseEnd_649860] using wordTrace_append hprefix tailTrace_649860
  have hstable : (prefixWord ++ tailWord_649860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649860).length < 2 ^ (prefixWord ++ tailWord_649860).sum := by decide
  have hdescent : baseEnd_649860 < baseStart_649860 := by decide
  rcases family_descends (prefixWord ++ tailWord_649860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649906 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_649906 : Nat := 118140960795 + 649906 * 2 ^ 59
def prefixEnd_649906 : Nat := 4983230072969 + 3 ^ 40 * 649906 * 2
def baseEnd_649906 : Nat := 296634807325368420876571

theorem tailTrace_649906 : CollatzResearch.WordTrace tailWord_649906 prefixEnd_649906 296634807325368420876571 := by
  unfold tailWord_649906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926004795877257988284393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15802679455672687968758381 5926004795877257988284393)
  ·
    refine ⟨4444503596907943491213295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5926004795877257988284393 4444503596907943491213295)
    ·
      refine ⟨6666755395361915236819943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444503596907943491213295 6666755395361915236819943)
      ·
        refine ⟨10000133093042872855229915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666755395361915236819943 10000133093042872855229915)
        ·
          refine ⟨15000199639564309282844873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000133093042872855229915 15000199639564309282844873)
          ·
            refine ⟨11250149729673231962133655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15000199639564309282844873 11250149729673231962133655)
            ·
              refine ⟨16875224594509847943200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11250149729673231962133655 16875224594509847943200483)
              ·
                refine ⟨25312836891764771914800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16875224594509847943200483 25312836891764771914800725)
                ·
                  refine ⟨296634807325368420876571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25312836891764771914800725 296634807325368420876571)
                  ·
                    rfl

theorem cell20_649906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_649906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649906 prefixEnd_649906 := by exact prefixLift 649906
  have htrace : WordTrace (prefixWord ++ tailWord_649906) baseStart_649906 baseEnd_649906 := by
    simpa [prefixWord, tailWord_649906, baseEnd_649906] using wordTrace_append hprefix tailTrace_649906
  have hstable : (prefixWord ++ tailWord_649906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649906).length < 2 ^ (prefixWord ++ tailWord_649906).sum := by decide
  have hdescent : baseEnd_649906 < baseStart_649906 := by decide
  rcases family_descends (prefixWord ++ tailWord_649906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649957 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 2]
def baseStart_649957 : Nat := 118140960795 + 649957 * 2 ^ 59
def prefixEnd_649957 : Nat := 4983230072969 + 3 ^ 40 * 649957 * 2
def baseEnd_649957 : Nat := 296658085115038910176363

theorem tailTrace_649957 : CollatzResearch.WordTrace tailWord_649957 prefixEnd_649957 296658085115038910176363 := by
  unfold tailWord_649957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23705879306324267663244125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15803919537549511775496083 23705879306324267663244125)
  ·
    refine ⟨8889704739871600373716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23705879306324267663244125 8889704739871600373716547)
    ·
      refine ⟨13334557109807400560574821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889704739871600373716547 13334557109807400560574821)
      ·
        refine ⟨2500229458088887605107779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13334557109807400560574821 2500229458088887605107779)
        ·
          refine ⟨3750344187133331407661669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500229458088887605107779 3750344187133331407661669)
          ·
            refine ⟨703189535087499638936563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3750344187133331407661669 703189535087499638936563)
            ·
              refine ⟨1054784302631249458404845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703189535087499638936563 1054784302631249458404845)
              ·
                refine ⟨395544113486718546901817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054784302631249458404845 395544113486718546901817)
                ·
                  refine ⟨296658085115038910176363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395544113486718546901817 296658085115038910176363)
                  ·
                    rfl

theorem cell20_649957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_649957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649957 prefixEnd_649957 := by exact prefixLift 649957
  have htrace : WordTrace (prefixWord ++ tailWord_649957) baseStart_649957 baseEnd_649957 := by
    simpa [prefixWord, tailWord_649957, baseEnd_649957] using wordTrace_append hprefix tailTrace_649957
  have hstable : (prefixWord ++ tailWord_649957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649957).length < 2 ^ (prefixWord ++ tailWord_649957).sum := by decide
  have hdescent : baseEnd_649957 < baseStart_649957 := by decide
  rcases family_descends (prefixWord ++ tailWord_649957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649975 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_649975 : Nat := 118140960795 + 649975 * 2 ^ 59
def prefixEnd_649975 : Nat := 4983230072969 + 3 ^ 40 * 649975 * 2
def baseEnd_649975 : Nat := 296666300805510847576289

theorem tailTrace_649975 : CollatzResearch.WordTrace tailWord_649975 prefixEnd_649975 296666300805510847576289 := by
  unfold tailWord_649975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23706535820259056737399379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15804357213506037824932919 23706535820259056737399379)
  ·
    refine ⟨35559803730388585106099069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23706535820259056737399379 35559803730388585106099069)
    ·
      refine ⟨13334926398895719414787151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35559803730388585106099069 13334926398895719414787151)
      ·
        refine ⟨20002389598343579122180727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13334926398895719414787151 20002389598343579122180727)
        ·
          refine ⟨30003584397515368683271091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20002389598343579122180727 30003584397515368683271091)
          ·
            refine ⟨45005376596273053024906637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30003584397515368683271091 45005376596273053024906637)
            ·
              refine ⟨16877016223602394884339989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45005376596273053024906637 16877016223602394884339989)
              ·
                refine ⟨791110135481362260203437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16877016223602394884339989 791110135481362260203437)
                ·
                  refine ⟨296666300805510847576289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791110135481362260203437 296666300805510847576289)
                  ·
                    rfl

theorem cell20_649975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_649975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649975 prefixEnd_649975 := by exact prefixLift 649975
  have htrace : WordTrace (prefixWord ++ tailWord_649975) baseStart_649975 baseEnd_649975 := by
    simpa [prefixWord, tailWord_649975, baseEnd_649975] using wordTrace_append hprefix tailTrace_649975
  have hstable : (prefixWord ++ tailWord_649975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649975).length < 2 ^ (prefixWord ++ tailWord_649975).sum := by decide
  have hdescent : baseEnd_649975 < baseStart_649975 := by decide
  rcases family_descends (prefixWord ++ tailWord_649975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649992 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_649992 : Nat := 118140960795 + 649992 * 2 ^ 59
def prefixEnd_649992 : Nat := 4983230072969 + 3 ^ 40 * 649992 * 2
def baseEnd_649992 : Nat := 296674060068734344009553

theorem tailTrace_649992 : CollatzResearch.WordTrace tailWord_649992 prefixEnd_649992 296674060068734344009553 := by
  unfold tailWord_649992
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853577930598734320384115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15804770574131645760512153 11853577930598734320384115)
  ·
    refine ⟨17780366895898101480576173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11853577930598734320384115 17780366895898101480576173)
    ·
      refine ⟨6667637585961788055216065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17780366895898101480576173 6667637585961788055216065)
      ·
        refine ⟨5000728189471341041412049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6667637585961788055216065 5000728189471341041412049)
        ·
          refine ⟨3750546142103505781059037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5000728189471341041412049 3750546142103505781059037)
          ·
            refine ⟨1406454803288814667897139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3750546142103505781059037 1406454803288814667897139)
            ·
              refine ⟨2109682204933222001845709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406454803288814667897139 2109682204933222001845709)
              ·
                refine ⟨791130826849958250692141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109682204933222001845709 791130826849958250692141)
                ·
                  refine ⟨296674060068734344009553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791130826849958250692141 296674060068734344009553)
                  ·
                    rfl

theorem cell20_649992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_649992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649992 prefixEnd_649992 := by exact prefixLift 649992
  have htrace : WordTrace (prefixWord ++ tailWord_649992) baseStart_649992 baseEnd_649992 := by
    simpa [prefixWord, tailWord_649992, baseEnd_649992] using wordTrace_append hprefix tailTrace_649992
  have hstable : (prefixWord ++ tailWord_649992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649992).length < 2 ^ (prefixWord ++ tailWord_649992).sum := by decide
  have hdescent : baseEnd_649992 < baseStart_649992 := by decide
  rcases family_descends (prefixWord ++ tailWord_649992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650026 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_650026 : Nat := 118140960795 + 650026 * 2 ^ 59
def prefixEnd_650026 : Nat := 4983230072969 + 3 ^ 40 * 650026 * 2
def baseEnd_650026 : Nat := 296689578595181336876081

theorem tailTrace_650026 : CollatzResearch.WordTrace tailWord_650026 prefixEnd_650026 296689578595181336876081 := by
  unfold tailWord_650026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927098985768573111876483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15805597295382861631670621 5927098985768573111876483)
  ·
    refine ⟨8890648478652859667814725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5927098985768573111876483 8890648478652859667814725)
    ·
      refine ⟨1666996589747411187715261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8890648478652859667814725 1666996589747411187715261)
      ·
        refine ⟨625123721155279195393223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1666996589747411187715261 625123721155279195393223)
        ·
          refine ⟨937685581732918793089835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625123721155279195393223 937685581732918793089835)
          ·
            refine ⟨1406528372599378189634753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937685581732918793089835 1406528372599378189634753)
            ·
              refine ⟨1054896279449533642226065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406528372599378189634753 1054896279449533642226065)
              ·
                refine ⟨791172209587150231669549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054896279449533642226065 791172209587150231669549)
                ·
                  refine ⟨296689578595181336876081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791172209587150231669549 296689578595181336876081)
                  ·
                    rfl

theorem cell20_650026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_650026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650026 prefixEnd_650026 := by exact prefixLift 650026
  have htrace : WordTrace (prefixWord ++ tailWord_650026) baseStart_650026 baseEnd_650026 := by
    simpa [prefixWord, tailWord_650026, baseEnd_650026] using wordTrace_append hprefix tailTrace_650026
  have hstable : (prefixWord ++ tailWord_650026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650026).length < 2 ^ (prefixWord ++ tailWord_650026).sum := by decide
  have hdescent : baseEnd_650026 < baseStart_650026 := by decide
  rcases family_descends (prefixWord ++ tailWord_650026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650051 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_650051 : Nat := 118140960795 + 650051 * 2 ^ 59
def prefixEnd_650051 : Nat := 4983230072969 + 3 ^ 40 * 650051 * 2
def baseEnd_650051 : Nat := 296700989276392361042645

theorem tailTrace_650051 : CollatzResearch.WordTrace tailWord_650051 prefixEnd_650051 296700989276392361042645 := by
  unfold tailWord_650051
  simp only [CollatzResearch.WordTrace]
  refine ⟨23709307767983721717166007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15806205178655814478110671 23709307767983721717166007)
  ·
    refine ⟨35563961651975582575749011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23709307767983721717166007 35563961651975582575749011)
    ·
      refine ⟨53345942477963373863623517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35563961651975582575749011 53345942477963373863623517)
      ·
        refine ⟨20004728429236265198858819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53345942477963373863623517 20004728429236265198858819)
        ·
          refine ⟨30007092643854397798288229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20004728429236265198858819 30007092643854397798288229)
          ·
            refine ⟨5626329870722699587179043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30007092643854397798288229 5626329870722699587179043)
            ·
              refine ⟨8439494806084049380768565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626329870722699587179043 8439494806084049380768565)
              ·
                refine ⟨791202638070379629447053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8439494806084049380768565 791202638070379629447053)
                ·
                  refine ⟨296700989276392361042645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791202638070379629447053 296700989276392361042645)
                  ·
                    rfl

theorem cell20_650051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_650051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650051 prefixEnd_650051 := by exact prefixLift 650051
  have htrace : WordTrace (prefixWord ++ tailWord_650051) baseStart_650051 baseEnd_650051 := by
    simpa [prefixWord, tailWord_650051, baseEnd_650051] using wordTrace_append hprefix tailTrace_650051
  have hstable : (prefixWord ++ tailWord_650051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650051).length < 2 ^ (prefixWord ++ tailWord_650051).sum := by decide
  have hdescent : baseEnd_650051 < baseStart_650051 := by decide
  rcases family_descends (prefixWord ++ tailWord_650051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650096 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_650096 : Nat := 118140960795 + 650096 * 2 ^ 59
def prefixEnd_650096 : Nat := 4983230072969 + 3 ^ 40 * 650096 * 2
def baseEnd_650096 : Nat := 296721528502572204542461

theorem tailTrace_650096 : CollatzResearch.WordTrace tailWord_650096 prefixEnd_650096 296721528502572204542461 := by
  unfold tailWord_650096
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855474526410347201277071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15807299368547129601702761 11855474526410347201277071)
  ·
    refine ⟨17783211789615520801915607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11855474526410347201277071 17783211789615520801915607)
    ·
      refine ⟨26674817684423281202873411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17783211789615520801915607 26674817684423281202873411)
      ·
        refine ⟨40012226526634921804310117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26674817684423281202873411 40012226526634921804310117)
        ·
          refine ⟨7502292473744047838308147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40012226526634921804310117 7502292473744047838308147)
          ·
            refine ⟨11253438710616071757462221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502292473744047838308147 11253438710616071757462221)
            ·
              refine ⟨4220039516481026909048333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11253438710616071757462221 4220039516481026909048333)
              ·
                refine ⟨1582514818680385090893125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4220039516481026909048333 1582514818680385090893125)
                ·
                  refine ⟨296721528502572204542461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582514818680385090893125 296721528502572204542461)
                  ·
                    rfl

theorem cell20_650096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_650096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650096 prefixEnd_650096 := by exact prefixLift 650096
  have htrace : WordTrace (prefixWord ++ tailWord_650096) baseStart_650096 baseEnd_650096 := by
    simpa [prefixWord, tailWord_650096, baseEnd_650096] using wordTrace_append hprefix tailTrace_650096
  have hstable : (prefixWord ++ tailWord_650096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650096).length < 2 ^ (prefixWord ++ tailWord_650096).sum := by decide
  have hdescent : baseEnd_650096 < baseStart_650096 := by decide
  rcases family_descends (prefixWord ++ tailWord_650096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650102 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_650102 : Nat := 118140960795 + 650102 * 2 ^ 59
def prefixEnd_650102 : Nat := 4983230072969 + 3 ^ 40 * 650102 * 2
def baseEnd_650102 : Nat := 296724267066062850342437

theorem tailTrace_650102 : CollatzResearch.WordTrace tailWord_650102 prefixEnd_650102 296724267066062850342437 := by
  unfold tailWord_650102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481947993174934839204535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15807445260532638284848373 1481947993174934839204535)
  ·
    refine ⟨2222921989762402258806803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481947993174934839204535 2222921989762402258806803)
    ·
      refine ⟨3334382984643603388210205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222921989762402258806803 3334382984643603388210205)
      ·
        refine ⟨1250393619241351270578827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3334382984643603388210205 1250393619241351270578827)
        ·
          refine ⟨1875590428862026905868241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250393619241351270578827 1875590428862026905868241)
          ·
            refine ⟨1406692821646520179401181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875590428862026905868241 1406692821646520179401181)
            ·
              refine ⟨527509808117445067275443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406692821646520179401181 527509808117445067275443)
              ·
                refine ⟨791264712176167600913165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527509808117445067275443 791264712176167600913165)
                ·
                  refine ⟨296724267066062850342437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791264712176167600913165 296724267066062850342437)
                  ·
                    rfl

theorem cell20_650102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_650102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650102 prefixEnd_650102 := by exact prefixLift 650102
  have htrace : WordTrace (prefixWord ++ tailWord_650102) baseStart_650102 baseEnd_650102 := by
    simpa [prefixWord, tailWord_650102, baseEnd_650102] using wordTrace_append hprefix tailTrace_650102
  have hstable : (prefixWord ++ tailWord_650102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650102).length < 2 ^ (prefixWord ++ tailWord_650102).sum := by decide
  have hdescent : baseEnd_650102 < baseStart_650102 := by decide
  rcases family_descends (prefixWord ++ tailWord_650102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650120 : List Nat := [2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_650120 : Nat := 118140960795 + 650120 * 2 ^ 59
def prefixEnd_650120 : Nat := 4983230072969 + 3 ^ 40 * 650120 * 2
def baseEnd_650120 : Nat := 98910827585511595914121

theorem tailTrace_650120 : CollatzResearch.WordTrace tailWord_650120 prefixEnd_650120 98910827585511595914121 := by
  unfold tailWord_650120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855912202366873250713907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15807882936489164334285209 11855912202366873250713907)
  ·
    refine ⟨17783868303550309876070861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11855912202366873250713907 17783868303550309876070861)
    ·
      refine ⟨6668950613831366203526573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17783868303550309876070861 6668950613831366203526573)
      ·
        refine ⟨2500856480186762326322465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6668950613831366203526573 2500856480186762326322465)
        ·
          refine ⟨1875642360140071744741849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2500856480186762326322465 1875642360140071744741849)
          ·
            refine ⟨1406731770105053808556387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875642360140071744741849 1406731770105053808556387)
            ·
              refine ⟨2110097655157580712834581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406731770105053808556387 2110097655157580712834581)
              ·
                refine ⟨98910827585511595914121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2110097655157580712834581 98910827585511595914121)
                ·
                  rfl

theorem cell20_650120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_650120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650120 prefixEnd_650120 := by exact prefixLift 650120
  have htrace : WordTrace (prefixWord ++ tailWord_650120) baseStart_650120 baseEnd_650120 := by
    simpa [prefixWord, tailWord_650120, baseEnd_650120] using wordTrace_append hprefix tailTrace_650120
  have hstable : (prefixWord ++ tailWord_650120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650120).length < 2 ^ (prefixWord ++ tailWord_650120).sum := by decide
  have hdescent : baseEnd_650120 < baseStart_650120 := by decide
  rcases family_descends (prefixWord ++ tailWord_650120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650157 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_650157 : Nat := 118140960795 + 650157 * 2 ^ 59
def prefixEnd_650157 : Nat := 4983230072969 + 3 ^ 40 * 650157 * 2
def baseEnd_650157 : Nat := 296749370564727103508879

theorem tailTrace_650157 : CollatzResearch.WordTrace tailWord_650157 prefixEnd_650157 296749370564727103508879 := by
  unfold tailWord_650157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23713173905599701820524725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15808782603733134547016483 23713173905599701820524725)
  ·
    refine ⟨2223110053649972045674193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23713173905599701820524725 2223110053649972045674193)
    ·
      refine ⟨1667332540237479034255645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2223110053649972045674193 1667332540237479034255645)
      ·
        refine ⟨625249702589054637845867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1667332540237479034255645 625249702589054637845867)
        ·
          refine ⟨937874553883581956768801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625249702589054637845867 937874553883581956768801)
          ·
            refine ⟨703405915412686467576601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937874553883581956768801 703405915412686467576601)
            ·
              refine ⟨527554436559514850682451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703405915412686467576601 527554436559514850682451)
              ·
                refine ⟨791331654839272276023677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527554436559514850682451 791331654839272276023677)
                ·
                  refine ⟨296749370564727103508879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791331654839272276023677 296749370564727103508879)
                  ·
                    rfl

theorem cell20_650157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_650157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650157 prefixEnd_650157 := by exact prefixLift 650157
  have htrace : WordTrace (prefixWord ++ tailWord_650157) baseStart_650157 baseEnd_650157 := by
    simpa [prefixWord, tailWord_650157, baseEnd_650157] using wordTrace_append hprefix tailTrace_650157
  have hstable : (prefixWord ++ tailWord_650157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650157).length < 2 ^ (prefixWord ++ tailWord_650157).sum := by decide
  have hdescent : baseEnd_650157 < baseStart_650157 := by decide
  rcases family_descends (prefixWord ++ tailWord_650157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650224 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_650224 : Nat := 118140960795 + 650224 * 2 ^ 59
def prefixEnd_650224 : Nat := 4983230072969 + 3 ^ 40 * 650224 * 2
def baseEnd_650224 : Nat := 296779951190372648275271

theorem tailTrace_650224 : CollatzResearch.WordTrace tailWord_650224 prefixEnd_650224 296779951190372648275271 := by
  unfold tailWord_650224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857808798178486131606863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15810411730904648175475817 11857808798178486131606863)
  ·
    refine ⟨17786713197267729197410295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11857808798178486131606863 17786713197267729197410295)
    ·
      refine ⟨26680069795901593796115443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17786713197267729197410295 26680069795901593796115443)
      ·
        refine ⟨40020104693852390694173165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26680069795901593796115443 40020104693852390694173165)
        ·
          refine ⟨15007539260194646510314937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40020104693852390694173165 15007539260194646510314937)
          ·
            refine ⟨11255654445145984882736203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007539260194646510314937 11255654445145984882736203)
            ·
              refine ⟨16883481667718977324104305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255654445145984882736203 16883481667718977324104305)
              ·
                refine ⟨12662611250789232993078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16883481667718977324104305 12662611250789232993078229)
                ·
                  refine ⟨296779951190372648275271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12662611250789232993078229 296779951190372648275271)
                  ·
                    rfl

theorem cell20_650224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_650224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650224 prefixEnd_650224 := by exact prefixLift 650224
  have htrace : WordTrace (prefixWord ++ tailWord_650224) baseStart_650224 baseEnd_650224 := by
    simpa [prefixWord, tailWord_650224, baseEnd_650224] using wordTrace_append hprefix tailTrace_650224
  have hstable : (prefixWord ++ tailWord_650224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650224).length < 2 ^ (prefixWord ++ tailWord_650224).sum := by decide
  have hdescent : baseEnd_650224 < baseStart_650224 := by decide
  rcases family_descends (prefixWord ++ tailWord_650224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650265 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 2]
def baseStart_650265 : Nat := 118140960795 + 650265 * 2 ^ 59
def prefixEnd_650265 : Nat := 4983230072969 + 3 ^ 40 * 650265 * 2
def baseEnd_650265 : Nat := 296798664707558727908437

theorem tailTrace_650265 : CollatzResearch.WordTrace tailWord_650265 prefixEnd_650265 296798664707558727908437 := by
  unfold tailWord_650265
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717112989208436265456249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811408659472290843637499 23717112989208436265456249)
  ·
    refine ⟨17787834741906327199092187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23717112989208436265456249 17787834741906327199092187)
    ·
      refine ⟨26681752112859490798638281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17787834741906327199092187 26681752112859490798638281)
      ·
        refine ⟨20011314084644618098978711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26681752112859490798638281 20011314084644618098978711)
        ·
          refine ⟨30016971126966927148468067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20011314084644618098978711 30016971126966927148468067)
          ·
            refine ⟨45025456690450390722702101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30016971126966927148468067 45025456690450390722702101)
            ·
              refine ⟨2110568282364862065126661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45025456690450390722702101 2110568282364862065126661)
              ·
                refine ⟨395731552943411637211249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2110568282364862065126661 395731552943411637211249)
                ·
                  refine ⟨296798664707558727908437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395731552943411637211249 296798664707558727908437)
                  ·
                    rfl

theorem cell20_650265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_650265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650265 prefixEnd_650265 := by exact prefixLift 650265
  have htrace : WordTrace (prefixWord ++ tailWord_650265) baseStart_650265 baseEnd_650265 := by
    simpa [prefixWord, tailWord_650265, baseEnd_650265] using wordTrace_append hprefix tailTrace_650265
  have hstable : (prefixWord ++ tailWord_650265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650265).length < 2 ^ (prefixWord ++ tailWord_650265).sum := by decide
  have hdescent : baseEnd_650265 < baseStart_650265 := by decide
  rcases family_descends (prefixWord ++ tailWord_650265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650326 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_650326 : Nat := 118140960795 + 650326 * 2 ^ 59
def prefixEnd_650326 : Nat := 4983230072969 + 3 ^ 40 * 650326 * 2
def baseEnd_650326 : Nat := 296826506769713626874855

theorem tailTrace_650326 : CollatzResearch.WordTrace tailWord_650326 prefixEnd_650326 296826506769713626874855 := by
  unfold tailWord_650326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482458615124215230214177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15812891894658295788951221 1482458615124215230214177)
  ·
    refine ⟨1111843961343161422660633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1482458615124215230214177 1111843961343161422660633)
    ·
      refine ⟨833882971007371066995475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1111843961343161422660633 833882971007371066995475)
      ·
        refine ⟨1250824456511056600493213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833882971007371066995475 1250824456511056600493213)
        ·
          refine ⟨469059171191646225184955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1250824456511056600493213 469059171191646225184955)
          ·
            refine ⟨703588756787469337777433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469059171191646225184955 703588756787469337777433)
            ·
              refine ⟨527691567590602003333075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703588756787469337777433 527691567590602003333075)
              ·
                refine ⟨791537351385903004999613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527691567590602003333075 791537351385903004999613)
                ·
                  refine ⟨296826506769713626874855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791537351385903004999613 296826506769713626874855)
                  ·
                    rfl

theorem cell20_650326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_650326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650326 prefixEnd_650326 := by exact prefixLift 650326
  have htrace : WordTrace (prefixWord ++ tailWord_650326) baseStart_650326 baseEnd_650326 := by
    simpa [prefixWord, tailWord_650326, baseEnd_650326] using wordTrace_append hprefix tailTrace_650326
  have hstable : (prefixWord ++ tailWord_650326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650326).length < 2 ^ (prefixWord ++ tailWord_650326).sum := by decide
  have hdescent : baseEnd_650326 < baseStart_650326 := by decide
  rcases family_descends (prefixWord ++ tailWord_650326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650358 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_650358 : Nat := 118140960795 + 650358 * 2 ^ 59
def prefixEnd_650358 : Nat := 4983230072969 + 3 ^ 40 * 650358 * 2
def baseEnd_650358 : Nat := 296841112441663737808057

theorem tailTrace_650358 : CollatzResearch.WordTrace tailWord_650358 prefixEnd_650358 296841112441663737808057 := by
  unfold tailWord_650358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482531561116969571786983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15813669985247675432394485 1482531561116969571786983)
  ·
    refine ⟨2223797341675454357680475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482531561116969571786983 2223797341675454357680475)
    ·
      refine ⟨3335696012513181536520713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2223797341675454357680475 3335696012513181536520713)
      ·
        refine ⟨2501772009384886152390535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335696012513181536520713 2501772009384886152390535)
        ·
          refine ⟨3752658014077329228585803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501772009384886152390535 3752658014077329228585803)
          ·
            refine ⟨5628987021115993842878705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752658014077329228585803 5628987021115993842878705)
            ·
              refine ⟨4221740265836995382159029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5628987021115993842878705 4221740265836995382159029)
              ·
                refine ⟨395788149922218317077409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4221740265836995382159029 395788149922218317077409)
                ·
                  refine ⟨296841112441663737808057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395788149922218317077409 296841112441663737808057)
                  ·
                    rfl

theorem cell20_650358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_650358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650358 prefixEnd_650358 := by exact prefixLift 650358
  have htrace : WordTrace (prefixWord ++ tailWord_650358) baseStart_650358 baseEnd_650358 := by
    simpa [prefixWord, tailWord_650358, baseEnd_650358] using wordTrace_append hprefix tailTrace_650358
  have hstable : (prefixWord ++ tailWord_650358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650358).length < 2 ^ (prefixWord ++ tailWord_650358).sum := by decide
  have hdescent : baseEnd_650358 < baseStart_650358 := by decide
  rcases family_descends (prefixWord ++ tailWord_650358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650369 : List Nat := [1, 2, 4, 2, 2, 9]
def baseStart_650369 : Nat := 118140960795 + 650369 * 2 ^ 59
def prefixEnd_650369 : Nat := 4983230072969 + 3 ^ 40 * 650369 * 2
def baseEnd_650369 : Nat := 10994301227459132905235

theorem tailTrace_650369 : CollatzResearch.WordTrace tailWord_650369 prefixEnd_650369 10994301227459132905235 := by
  unfold tailWord_650369
  simp only [CollatzResearch.WordTrace]
  refine ⟨23720906180831662027242161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15813937453887774684828107 23720906180831662027242161)
  ·
    refine ⟨17790679635623746520431621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23720906180831662027242161 17790679635623746520431621)
    ·
      refine ⟨3335752431679452472580929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17790679635623746520431621 3335752431679452472580929)
      ·
        refine ⟨2501814323759589354435697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335752431679452472580929 2501814323759589354435697)
        ·
          refine ⟨1876360742819692015826773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2501814323759589354435697 1876360742819692015826773)
          ·
            refine ⟨10994301227459132905235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1876360742819692015826773 10994301227459132905235)
            ·
              rfl

theorem cell20_650369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_650369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650369 prefixEnd_650369 := by exact prefixLift 650369
  have htrace : WordTrace (prefixWord ++ tailWord_650369) baseStart_650369 baseEnd_650369 := by
    simpa [prefixWord, tailWord_650369, baseEnd_650369] using wordTrace_append hprefix tailTrace_650369
  have hstable : (prefixWord ++ tailWord_650369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650369).length < 2 ^ (prefixWord ++ tailWord_650369).sum := by decide
  have hdescent : baseEnd_650369 < baseStart_650369 := by decide
  rcases family_descends (prefixWord ++ tailWord_650369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650372 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_650372 : Nat := 118140960795 + 650372 * 2 ^ 59
def prefixEnd_650372 : Nat := 4983230072969 + 3 ^ 40 * 650372 * 2
def baseEnd_650372 : Nat := 296847502423141911341333

theorem tailTrace_650372 : CollatzResearch.WordTrace tailWord_650372 prefixEnd_650372 296847502423141911341333 := by
  unfold tailWord_650372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860507799910396769800685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15814010399880529026400913 11860507799910396769800685)
  ·
    refine ⟨4447690424966398788675257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11860507799910396769800685 4447690424966398788675257)
    ·
      refine ⟨3335767818724799091506443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4447690424966398788675257 3335767818724799091506443)
      ·
        refine ⟨5003651728087198637259665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3335767818724799091506443 5003651728087198637259665)
        ·
          refine ⟨3752738796065398977944749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5003651728087198637259665 3752738796065398977944749)
          ·
            refine ⟨1407277048524524616729281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3752738796065398977944749 1407277048524524616729281)
            ·
              refine ⟨1055457786393393462546961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407277048524524616729281 1055457786393393462546961)
              ·
                refine ⟨791593339795045096910221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055457786393393462546961 791593339795045096910221)
                ·
                  refine ⟨296847502423141911341333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791593339795045096910221 296847502423141911341333)
                  ·
                    rfl

theorem cell20_650372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_650372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650372 prefixEnd_650372 := by exact prefixLift 650372
  have htrace : WordTrace (prefixWord ++ tailWord_650372) baseStart_650372 baseEnd_650372 := by
    simpa [prefixWord, tailWord_650372, baseEnd_650372] using wordTrace_append hprefix tailTrace_650372
  have hstable : (prefixWord ++ tailWord_650372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650372).length < 2 ^ (prefixWord ++ tailWord_650372).sum := by decide
  have hdescent : baseEnd_650372 < baseStart_650372 := by decide
  rcases family_descends (prefixWord ++ tailWord_650372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650386 : List Nat := [3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_650386 : Nat := 118140960795 + 650386 * 2 ^ 59
def prefixEnd_650386 : Nat := 4983230072969 + 3 ^ 40 * 650386 * 2
def baseEnd_650386 : Nat := 98951297468206694958203

theorem tailTrace_650386 : CollatzResearch.WordTrace tailWord_650386 prefixEnd_650386 98951297468206694958203 := by
  unfold tailWord_650386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930381555442518482652753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15814350814513382620407341 5930381555442518482652753)
  ·
    refine ⟨4447786166581888861989565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5930381555442518482652753 4447786166581888861989565)
    ·
      refine ⟨1667919812468208323246087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4447786166581888861989565 1667919812468208323246087)
      ·
        refine ⟨2501879718702312484869131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667919812468208323246087 2501879718702312484869131)
        ·
          refine ⟨3752819578053468727303697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501879718702312484869131 3752819578053468727303697)
          ·
            refine ⟨2814614683540101545477773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752819578053468727303697 2814614683540101545477773)
            ·
              refine ⟨1055480506327538079554165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814614683540101545477773 1055480506327538079554165)
              ·
                refine ⟨98951297468206694958203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055480506327538079554165 98951297468206694958203)
                ·
                  rfl

theorem cell20_650386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_650386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650386 prefixEnd_650386 := by exact prefixLift 650386
  have htrace : WordTrace (prefixWord ++ tailWord_650386) baseStart_650386 baseEnd_650386 := by
    simpa [prefixWord, tailWord_650386, baseEnd_650386] using wordTrace_append hprefix tailTrace_650386
  have hstable : (prefixWord ++ tailWord_650386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650386).length < 2 ^ (prefixWord ++ tailWord_650386).sum := by decide
  have hdescent : baseEnd_650386 < baseStart_650386 := by decide
  rcases family_descends (prefixWord ++ tailWord_650386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650400 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_650400 : Nat := 118140960795 + 650400 * 2 ^ 59
def prefixEnd_650400 : Nat := 4983230072969 + 3 ^ 40 * 650400 * 2
def baseEnd_650400 : Nat := 296860282386098258407885

theorem tailTrace_650400 : CollatzResearch.WordTrace tailWord_650400 prefixEnd_650400 296860282386098258407885 := by
  unfold tailWord_650400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11861018421859677160810327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15814691229146236214413769 11861018421859677160810327)
  ·
    refine ⟨17791527632789515741215491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11861018421859677160810327 17791527632789515741215491)
    ·
      refine ⟨26687291449184273611823237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17791527632789515741215491 26687291449184273611823237)
      ·
        refine ⟨5003867146722051302216857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26687291449184273611823237 5003867146722051302216857)
        ·
          refine ⟨3752900360041538476662643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5003867146722051302216857 3752900360041538476662643)
          ·
            refine ⟨5629350540062307714993965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752900360041538476662643 5629350540062307714993965)
            ·
              refine ⟨2111006452523365393122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5629350540062307714993965 2111006452523365393122737)
              ·
                refine ⟨1583254839392524044842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111006452523365393122737 1583254839392524044842053)
                ·
                  refine ⟨296860282386098258407885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583254839392524044842053 296860282386098258407885)
                  ·
                    rfl

theorem cell20_650400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_650400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650400 prefixEnd_650400 := by exact prefixLift 650400
  have htrace : WordTrace (prefixWord ++ tailWord_650400) baseStart_650400 baseEnd_650400 := by
    simpa [prefixWord, tailWord_650400, baseEnd_650400] using wordTrace_append hprefix tailTrace_650400
  have hstable : (prefixWord ++ tailWord_650400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650400).length < 2 ^ (prefixWord ++ tailWord_650400).sum := by decide
  have hdescent : baseEnd_650400 < baseStart_650400 := by decide
  rcases family_descends (prefixWord ++ tailWord_650400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650413 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 2]
def baseStart_650413 : Nat := 118140960795 + 650413 * 2 ^ 59
def prefixEnd_650413 : Nat := 4983230072969 + 3 ^ 40 * 650413 * 2
def baseEnd_650413 : Nat := 296866215940327990974499

theorem tailTrace_650413 : CollatzResearch.WordTrace tailWord_650413 prefixEnd_650413 296866215940327990974499 := by
  unfold tailWord_650413
  simp only [CollatzResearch.WordTrace]
  refine ⟨23722510992672257541843893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15815007328448171694562595 23722510992672257541843893)
  ·
    refine ⟨2223985405563024144547865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23722510992672257541843893 2223985405563024144547865)
    ·
      refine ⟨1667989054172268108410899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2223985405563024144547865 1667989054172268108410899)
      ·
        refine ⟨2501983581258402162616349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667989054172268108410899 2501983581258402162616349)
        ·
          refine ⟨938243842971900810981131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2501983581258402162616349 938243842971900810981131)
          ·
            refine ⟨1407365764457851216471697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938243842971900810981131 1407365764457851216471697)
            ·
              refine ⟨1055524323343388412353773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407365764457851216471697 1055524323343388412353773)
              ·
                refine ⟨395821621253770654632665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1055524323343388412353773 395821621253770654632665)
                ·
                  refine ⟨296866215940327990974499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395821621253770654632665 296866215940327990974499)
                  ·
                    rfl

theorem cell20_650413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_650413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650413 prefixEnd_650413 := by exact prefixLift 650413
  have htrace : WordTrace (prefixWord ++ tailWord_650413) baseStart_650413 baseEnd_650413 := by
    simpa [prefixWord, tailWord_650413, baseEnd_650413] using wordTrace_append hprefix tailTrace_650413
  have hstable : (prefixWord ++ tailWord_650413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650413).length < 2 ^ (prefixWord ++ tailWord_650413).sum := by decide
  have hdescent : baseEnd_650413 < baseStart_650413 := by decide
  rcases family_descends (prefixWord ++ tailWord_650413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650431 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_650431 : Nat := 118140960795 + 650431 * 2 ^ 59
def prefixEnd_650431 : Nat := 4983230072969 + 3 ^ 40 * 650431 * 2
def baseEnd_650431 : Nat := 296874431630799928374425

theorem tailTrace_650431 : CollatzResearch.WordTrace tailWord_650431 prefixEnd_650431 296874431630799928374425 := by
  unfold tailWord_650431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723167506607046615999147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15815445004404697743999431 23723167506607046615999147)
  ·
    refine ⟨35584751259910569923998721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23723167506607046615999147 35584751259910569923998721)
    ·
      refine ⟨26688563444932927442999041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35584751259910569923998721 26688563444932927442999041)
      ·
        refine ⟨20016422583699695582249281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26688563444932927442999041 20016422583699695582249281)
        ·
          refine ⟨15012316937774771686686961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20016422583699695582249281 15012316937774771686686961)
          ·
            refine ⟨11259237703331078765015221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15012316937774771686686961 11259237703331078765015221)
            ·
              refine ⟨1055553534687288634220177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11259237703331078765015221 1055553534687288634220177)
              ·
                refine ⟨791665151015466475665133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055553534687288634220177 791665151015466475665133)
                ·
                  refine ⟨296874431630799928374425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791665151015466475665133 296874431630799928374425)
                  ·
                    rfl

theorem cell20_650431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_650431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650431 prefixEnd_650431 := by exact prefixLift 650431
  have htrace : WordTrace (prefixWord ++ tailWord_650431) baseStart_650431 baseEnd_650431 := by
    simpa [prefixWord, tailWord_650431, baseEnd_650431] using wordTrace_append hprefix tailTrace_650431
  have hstable : (prefixWord ++ tailWord_650431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650431).length < 2 ^ (prefixWord ++ tailWord_650431).sum := by decide
  have hdescent : baseEnd_650431 < baseStart_650431 := by decide
  rcases family_descends (prefixWord ++ tailWord_650431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650483 : List Nat := [1, 1, 1, 2, 2, 7, 6]
def baseStart_650483 : Nat := 118140960795 + 650483 * 2 ^ 59
def prefixEnd_650483 : Nat := 4983230072969 + 3 ^ 40 * 650483 * 2
def baseEnd_650483 : Nat := 32988685094190984293431

theorem tailTrace_650483 : CollatzResearch.WordTrace tailWord_650483 prefixEnd_650483 32988685094190984293431 := by
  unfold tailWord_650483
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725064102418659496892103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15816709401612439664594735 23725064102418659496892103)
  ·
    refine ⟨35587596153627989245338155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725064102418659496892103 35587596153627989245338155)
    ·
      refine ⟨53381394230441983868007233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35587596153627989245338155 53381394230441983868007233)
      ·
        refine ⟨40036045672831487901005425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53381394230441983868007233 40036045672831487901005425)
        ·
          refine ⟨30027034254623615925754069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40036045672831487901005425 30027034254623615925754069)
          ·
            refine ⟨703758615342740998259861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30027034254623615925754069 703758615342740998259861)
            ·
              refine ⟨32988685094190984293431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 703758615342740998259861 32988685094190984293431)
              ·
                rfl

theorem cell20_650483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_650483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650483 prefixEnd_650483 := by exact prefixLift 650483
  have htrace : WordTrace (prefixWord ++ tailWord_650483) baseStart_650483 baseEnd_650483 := by
    simpa [prefixWord, tailWord_650483, baseEnd_650483] using wordTrace_append hprefix tailTrace_650483
  have hstable : (prefixWord ++ tailWord_650483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650483).length < 2 ^ (prefixWord ++ tailWord_650483).sum := by decide
  have hdescent : baseEnd_650483 < baseStart_650483 := by decide
  rcases family_descends (prefixWord ++ tailWord_650483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650490 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_650490 : Nat := 118140960795 + 650490 * 2 ^ 59
def prefixEnd_650490 : Nat := 4983230072969 + 3 ^ 40 * 650490 * 2
def baseEnd_650490 : Nat := 296901360838457945407517

theorem tailTrace_650490 : CollatzResearch.WordTrace tailWord_650490 prefixEnd_650490 296901360838457945407517 := by
  unfold tailWord_650490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931329853348324923099231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15816879608928866461597949 5931329853348324923099231)
  ·
    refine ⟨8896994780022487384648847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931329853348324923099231 8896994780022487384648847)
    ·
      refine ⟨13345492170033731076973271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8896994780022487384648847 13345492170033731076973271)
      ·
        refine ⟨20018238255050596615459907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13345492170033731076973271 20018238255050596615459907)
        ·
          refine ⟨30027357382575894923189861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20018238255050596615459907 30027357382575894923189861)
          ·
            refine ⟨5630129509232980298098099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30027357382575894923189861 5630129509232980298098099)
            ·
              refine ⟨8445194263849470447147149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630129509232980298098099 8445194263849470447147149)
              ·
                refine ⟨3166947848943551417680181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8445194263849470447147149 3166947848943551417680181)
                ·
                  refine ⟨296901360838457945407517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166947848943551417680181 296901360838457945407517)
                  ·
                    rfl

theorem cell20_650490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_650490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650490 prefixEnd_650490 := by exact prefixLift 650490
  have htrace : WordTrace (prefixWord ++ tailWord_650490) baseStart_650490 baseEnd_650490 := by
    simpa [prefixWord, tailWord_650490, baseEnd_650490] using wordTrace_append hprefix tailTrace_650490
  have hstable : (prefixWord ++ tailWord_650490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650490).length < 2 ^ (prefixWord ++ tailWord_650490).sum := by decide
  have hdescent : baseEnd_650490 < baseStart_650490 := by decide
  rcases family_descends (prefixWord ++ tailWord_650490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650500 : List Nat := [2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_650500 : Nat := 118140960795 + 650500 * 2 ^ 59
def prefixEnd_650500 : Nat := 4983230072969 + 3 ^ 40 * 650500 * 2
def baseEnd_650500 : Nat := 98968641703647451691381

theorem tailTrace_650500 : CollatzResearch.WordTrace tailWord_650500 prefixEnd_650500 98968641703647451691381 := by
  unfold tailWord_650500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862842071678535700130477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15817122762238047600173969 11862842071678535700130477)
  ·
    refine ⟨4448565776879450887548929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11862842071678535700130477 4448565776879450887548929)
    ·
      refine ⟨3336424332659588165661697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4448565776879450887548929 3336424332659588165661697)
      ·
        refine ⟨2502318249494691124246273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3336424332659588165661697 2502318249494691124246273)
        ·
          refine ⟨1876738687121018343184705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2502318249494691124246273 1876738687121018343184705)
          ·
            refine ⟨1407554015340763757388529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876738687121018343184705 1407554015340763757388529)
            ·
              refine ⟨1055665511505572818041397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407554015340763757388529 1055665511505572818041397)
              ·
                refine ⟨98968641703647451691381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055665511505572818041397 98968641703647451691381)
                ·
                  rfl

theorem cell20_650500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_650500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650500 prefixEnd_650500 := by exact prefixLift 650500
  have htrace : WordTrace (prefixWord ++ tailWord_650500) baseStart_650500 baseEnd_650500 := by
    simpa [prefixWord, tailWord_650500, baseEnd_650500] using wordTrace_append hprefix tailTrace_650500
  have hstable : (prefixWord ++ tailWord_650500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650500).length < 2 ^ (prefixWord ++ tailWord_650500).sum := by decide
  have hdescent : baseEnd_650500 < baseStart_650500 := by decide
  rcases family_descends (prefixWord ++ tailWord_650500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650507 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_650507 : Nat := 118140960795 + 650507 * 2 ^ 59
def prefixEnd_650507 : Nat := 4983230072969 + 3 ^ 40 * 650507 * 2
def baseEnd_650507 : Nat := 296909120101681441840781

theorem tailTrace_650507 : CollatzResearch.WordTrace tailWord_650507 prefixEnd_650507 296909120101681441840781 := by
  unfold tailWord_650507
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725939454331711595765775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15817292969554474397177183 23725939454331711595765775)
  ·
    refine ⟨35588909181497567393648663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725939454331711595765775 35588909181497567393648663)
    ·
      refine ⟨53383363772246351090472995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35588909181497567393648663 53383363772246351090472995)
      ·
        refine ⟨80075045658369526635709493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53383363772246351090472995 80075045658369526635709493)
        ·
          refine ⟨7507035530472143122097765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80075045658369526635709493 7507035530472143122097765)
          ·
            refine ⟨1407569161963526835393331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7507035530472143122097765 1407569161963526835393331)
            ·
              refine ⟨2111353742945290253089997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407569161963526835393331 2111353742945290253089997)
              ·
                refine ⟨791757653604483844908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2111353742945290253089997 791757653604483844908749)
                ·
                  refine ⟨296909120101681441840781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791757653604483844908749 296909120101681441840781)
                  ·
                    rfl

theorem cell20_650507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_650507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650507 prefixEnd_650507 := by exact prefixLift 650507
  have htrace : WordTrace (prefixWord ++ tailWord_650507) baseStart_650507 baseEnd_650507 := by
    simpa [prefixWord, tailWord_650507, baseEnd_650507] using wordTrace_append hprefix tailTrace_650507
  have hstable : (prefixWord ++ tailWord_650507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650507).length < 2 ^ (prefixWord ++ tailWord_650507).sum := by decide
  have hdescent : baseEnd_650507 < baseStart_650507 := by decide
  rcases family_descends (prefixWord ++ tailWord_650507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650541 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_650541 : Nat := 118140960795 + 650541 * 2 ^ 59
def prefixEnd_650541 : Nat := 4983230072969 + 3 ^ 40 * 650541 * 2
def baseEnd_650541 : Nat := 296924638628128434707309

theorem tailTrace_650541 : CollatzResearch.WordTrace tailWord_650541 prefixEnd_650541 296924638628128434707309 := by
  unfold tailWord_650541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727179536208535402503477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15818119690805690268335651 23727179536208535402503477)
  ·
    refine ⟨2224423081519550193984701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23727179536208535402503477 2224423081519550193984701)
    ·
      refine ⟨834158655569831322744263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2224423081519550193984701 834158655569831322744263)
      ·
        refine ⟨1251237983354746984116395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834158655569831322744263 1251237983354746984116395)
        ·
          refine ⟨1876856975032120476174593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251237983354746984116395 1876856975032120476174593)
          ·
            refine ⟨1407642731274090357130945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876856975032120476174593 1407642731274090357130945)
            ·
              refine ⟨1055732048455567767848209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407642731274090357130945 1055732048455567767848209)
              ·
                refine ⟨791799036341675825886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055732048455567767848209 791799036341675825886157)
                ·
                  refine ⟨296924638628128434707309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791799036341675825886157 296924638628128434707309)
                  ·
                    rfl

theorem cell20_650541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_650541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650541 prefixEnd_650541 := by exact prefixLift 650541
  have htrace : WordTrace (prefixWord ++ tailWord_650541) baseStart_650541 baseEnd_650541 := by
    simpa [prefixWord, tailWord_650541, baseEnd_650541] using wordTrace_append hprefix tailTrace_650541
  have hstable : (prefixWord ++ tailWord_650541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650541).length < 2 ^ (prefixWord ++ tailWord_650541).sum := by decide
  have hdescent : baseEnd_650541 < baseStart_650541 := by decide
  rcases family_descends (prefixWord ++ tailWord_650541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650545 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_650545 : Nat := 118140960795 + 650545 * 2 ^ 59
def prefixEnd_650545 : Nat := 4983230072969 + 3 ^ 40 * 650545 * 2
def baseEnd_650545 : Nat := 296926464337122198573959

theorem tailTrace_650545 : CollatzResearch.WordTrace tailWord_650545 prefixEnd_650545 296926464337122198573959 := by
  unfold tailWord_650545
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727325428194044085649089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15818216952129362723766059 23727325428194044085649089)
  ·
    refine ⟨17795494071145533064236817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23727325428194044085649089 17795494071145533064236817)
    ·
      refine ⟨13346620553359149798177613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17795494071145533064236817 13346620553359149798177613)
      ·
        refine ⟨5004982707509681174316605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13346620553359149798177613 5004982707509681174316605)
        ·
          refine ⟨1876868515316130440368727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5004982707509681174316605 1876868515316130440368727)
          ·
            refine ⟨2815302772974195660553091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876868515316130440368727 2815302772974195660553091)
            ·
              refine ⟨4222954159461293490829637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815302772974195660553091 4222954159461293490829637)
              ·
                refine ⟨791803904898992529530557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4222954159461293490829637 791803904898992529530557)
                ·
                  refine ⟨296926464337122198573959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791803904898992529530557 296926464337122198573959)
                  ·
                    rfl

theorem cell20_650545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_650545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650545 prefixEnd_650545 := by exact prefixLift 650545
  have htrace : WordTrace (prefixWord ++ tailWord_650545) baseStart_650545 baseEnd_650545 := by
    simpa [prefixWord, tailWord_650545, baseEnd_650545] using wordTrace_append hprefix tailTrace_650545
  have hstable : (prefixWord ++ tailWord_650545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650545).length < 2 ^ (prefixWord ++ tailWord_650545).sum := by decide
  have hdescent : baseEnd_650545 < baseStart_650545 := by decide
  rcases family_descends (prefixWord ++ tailWord_650545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650548 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_650548 : Nat := 118140960795 + 650548 * 2 ^ 59
def prefixEnd_650548 : Nat := 4983230072969 + 3 ^ 40 * 650548 * 2
def baseEnd_650548 : Nat := 296927833618867521473947

theorem tailTrace_650548 : CollatzResearch.WordTrace tailWord_650548 prefixEnd_650548 296927833618867521473947 := by
  unfold tailWord_650548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11863717423591587799004149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15818289898122117065338865 11863717423591587799004149)
  ·
    refine ⟨1112223508461711356156639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11863717423591587799004149 1112223508461711356156639)
    ·
      refine ⟨1668335262692567034234959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112223508461711356156639 1668335262692567034234959)
      ·
        refine ⟨2502502894038850551352439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668335262692567034234959 2502502894038850551352439)
        ·
          refine ⟨3753754341058275827028659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502502894038850551352439 3753754341058275827028659)
          ·
            refine ⟨5630631511587413740542989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753754341058275827028659 5630631511587413740542989)
            ·
              refine ⟨2111486816845280152703621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5630631511587413740542989 2111486816845280152703621)
              ·
                refine ⟨395903778158490028631929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2111486816845280152703621 395903778158490028631929)
                ·
                  refine ⟨296927833618867521473947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395903778158490028631929 296927833618867521473947)
                  ·
                    rfl

theorem cell20_650548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_650548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650548 prefixEnd_650548 := by exact prefixLift 650548
  have htrace : WordTrace (prefixWord ++ tailWord_650548) baseStart_650548 baseEnd_650548 := by
    simpa [prefixWord, tailWord_650548, baseEnd_650548] using wordTrace_append hprefix tailTrace_650548
  have hstable : (prefixWord ++ tailWord_650548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650548).length < 2 ^ (prefixWord ++ tailWord_650548).sum := by decide
  have hdescent : baseEnd_650548 < baseStart_650548 := by decide
  rcases family_descends (prefixWord ++ tailWord_650548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650559 : List Nat := [1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_650559 : Nat := 118140960795 + 650559 * 2 ^ 59
def prefixEnd_650559 : Nat := 4983230072969 + 3 ^ 40 * 650559 * 2
def baseEnd_650559 : Nat := 98977618106200124035745

theorem tailTrace_650559 : CollatzResearch.WordTrace tailWord_650559 prefixEnd_650559 98977618106200124035745 := by
  unfold tailWord_650559
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727836050143324476658731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15818557366762216317772487 23727836050143324476658731)
  ·
    refine ⟨35591754075214986714988097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23727836050143324476658731 35591754075214986714988097)
    ·
      refine ⟨26693815556411240036241073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35591754075214986714988097 26693815556411240036241073)
      ·
        refine ⟨20020361667308430027180805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26693815556411240036241073 20020361667308430027180805)
        ·
          refine ⟨3753817812620330630096401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20020361667308430027180805 3753817812620330630096401)
          ·
            refine ⟨2815363359465247972572301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753817812620330630096401 2815363359465247972572301)
            ·
              refine ⟨1055761259799467989714613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2815363359465247972572301 1055761259799467989714613)
              ·
                refine ⟨98977618106200124035745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055761259799467989714613 98977618106200124035745)
                ·
                  rfl

theorem cell20_650559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_650559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650559 prefixEnd_650559 := by exact prefixLift 650559
  have htrace : WordTrace (prefixWord ++ tailWord_650559) baseStart_650559 baseEnd_650559 := by
    simpa [prefixWord, tailWord_650559, baseEnd_650559] using wordTrace_append hprefix tailTrace_650559
  have hstable : (prefixWord ++ tailWord_650559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650559).length < 2 ^ (prefixWord ++ tailWord_650559).sum := by decide
  have hdescent : baseEnd_650559 < baseStart_650559 := by decide
  rcases family_descends (prefixWord ++ tailWord_650559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650628 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_650628 : Nat := 118140960795 + 650628 * 2 ^ 59
def prefixEnd_650628 : Nat := 4983230072969 + 3 ^ 40 * 650628 * 2
def baseEnd_650628 : Nat := 296964347798742798806953

theorem tailTrace_650628 : CollatzResearch.WordTrace tailWord_650628 prefixEnd_650628 296964347798742798806953 := by
  unfold tailWord_650628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11865176343446674630460269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15820235124595566173947025 11865176343446674630460269)
  ·
    refine ⟨4449441128792502986422601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11865176343446674630460269 4449441128792502986422601)
    ·
      refine ⟨3337080846594377239816951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4449441128792502986422601 3337080846594377239816951)
      ·
        refine ⟨5005621269891565859725427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337080846594377239816951 5005621269891565859725427)
        ·
          refine ⟨7508431904837348789588141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005621269891565859725427 7508431904837348789588141)
          ·
            refine ⟨2815661964314005796095553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7508431904837348789588141 2815661964314005796095553)
            ·
              refine ⟨2111746473235504347071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815661964314005796095553 2111746473235504347071665)
              ·
                refine ⟨1583809854926628260303749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111746473235504347071665 1583809854926628260303749)
                ·
                  refine ⟨296964347798742798806953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583809854926628260303749 296964347798742798806953)
                  ·
                    rfl

theorem cell20_650628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_650628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650628 prefixEnd_650628 := by exact prefixLift 650628
  have htrace : WordTrace (prefixWord ++ tailWord_650628) baseStart_650628 baseEnd_650628 := by
    simpa [prefixWord, tailWord_650628, baseEnd_650628] using wordTrace_append hprefix tailTrace_650628
  have hstable : (prefixWord ++ tailWord_650628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650628).length < 2 ^ (prefixWord ++ tailWord_650628).sum := by decide
  have hdescent : baseEnd_650628 < baseStart_650628 := by decide
  rcases family_descends (prefixWord ++ tailWord_650628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650645 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 2]
def baseStart_650645 : Nat := 118140960795 + 650645 * 2 ^ 59
def prefixEnd_650645 : Nat := 4983230072969 + 3 ^ 40 * 650645 * 2
def baseEnd_650645 : Nat := 296972107061966295240217

theorem tailTrace_650645 : CollatzResearch.WordTrace tailWord_650645 prefixEnd_650645 296972107061966295240217 := by
  unfold tailWord_650645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23730972727831761164289389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15820648485221174109526259 23730972727831761164289389)
  ·
    refine ⟨8899114772936910436608521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23730972727831761164289389 8899114772936910436608521)
    ·
      refine ⟨6674336079702682827456391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8899114772936910436608521 6674336079702682827456391)
      ·
        refine ⟨10011504119554024241184587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6674336079702682827456391 10011504119554024241184587)
        ·
          refine ⟨15017256179331036361776881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10011504119554024241184587 15017256179331036361776881)
          ·
            refine ⟨11262942134498277271332661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15017256179331036361776881 11262942134498277271332661)
            ·
              refine ⟨1055900825109213494187437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11262942134498277271332661 1055900825109213494187437)
              ·
                refine ⟨395962809415955060320289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1055900825109213494187437 395962809415955060320289)
                ·
                  refine ⟨296972107061966295240217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395962809415955060320289 296972107061966295240217)
                  ·
                    rfl

theorem cell20_650645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_650645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650645 prefixEnd_650645 := by exact prefixLift 650645
  have htrace : WordTrace (prefixWord ++ tailWord_650645) baseStart_650645 baseEnd_650645 := by
    simpa [prefixWord, tailWord_650645, baseEnd_650645] using wordTrace_append hprefix tailTrace_650645
  have hstable : (prefixWord ++ tailWord_650645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650645).length < 2 ^ (prefixWord ++ tailWord_650645).sum := by decide
  have hdescent : baseEnd_650645 < baseStart_650645 := by decide
  rcases family_descends (prefixWord ++ tailWord_650645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650673 : List Nat := [1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_650673 : Nat := 118140960795 + 650673 * 2 ^ 59
def prefixEnd_650673 : Nat := 4983230072969 + 3 ^ 40 * 650673 * 2
def baseEnd_650673 : Nat := 98994962341640880768923

theorem tailTrace_650673 : CollatzResearch.WordTrace tailWord_650673 prefixEnd_650673 98994962341640880768923 := by
  unfold tailWord_650673
  simp only [CollatzResearch.WordTrace]
  refine ⟨23731993971730321946308673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15821329314486881297539115 23731993971730321946308673)
  ·
    refine ⟨17798995478797741459731505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23731993971730321946308673 17798995478797741459731505)
    ·
      refine ⟨13349246609098306094798629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17798995478797741459731505 13349246609098306094798629)
      ·
        refine ⟨2502983739205932392774743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13349246609098306094798629 2502983739205932392774743)
        ·
          refine ⟨3754475608808898589162115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502983739205932392774743 3754475608808898589162115)
          ·
            refine ⟨5631713413213347883743173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754475608808898589162115 5631713413213347883743173)
            ·
              refine ⟨1055946264977502728201845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5631713413213347883743173 1055946264977502728201845)
              ·
                refine ⟨98994962341640880768923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055946264977502728201845 98994962341640880768923)
                ·
                  rfl

theorem cell20_650673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_650673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650673 prefixEnd_650673 := by exact prefixLift 650673
  have htrace : WordTrace (prefixWord ++ tailWord_650673) baseStart_650673 baseEnd_650673 := by
    simpa [prefixWord, tailWord_650673, baseEnd_650673] using wordTrace_append hprefix tailTrace_650673
  have hstable : (prefixWord ++ tailWord_650673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650673).length < 2 ^ (prefixWord ++ tailWord_650673).sum := by decide
  have hdescent : baseEnd_650673 < baseStart_650673 := by decide
  rcases family_descends (prefixWord ++ tailWord_650673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650687 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_650687 : Nat := 118140960795 + 650687 * 2 ^ 59
def prefixEnd_650687 : Nat := 4983230072969 + 3 ^ 40 * 650687 * 2
def baseEnd_650687 : Nat := 296991277006400815840045

theorem tailTrace_650687 : CollatzResearch.WordTrace tailWord_650687 prefixEnd_650687 296991277006400815840045 := by
  unfold tailWord_650687
  simp only [CollatzResearch.WordTrace]
  refine ⟨23732504593679602337318315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15821669729119734891545543 23732504593679602337318315)
  ·
    refine ⟨35598756890519403505977473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23732504593679602337318315 35598756890519403505977473)
    ·
      refine ⟨26699067667889552629483105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35598756890519403505977473 26699067667889552629483105)
      ·
        refine ⟨20024300750917164472112329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26699067667889552629483105 20024300750917164472112329)
        ·
          refine ⟨15018225563187873354084247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20024300750917164472112329 15018225563187873354084247)
          ·
            refine ⟨22527338344781810031126371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15018225563187873354084247 22527338344781810031126371)
            ·
              refine ⟨33791007517172715046689557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22527338344781810031126371 33791007517172715046689557)
              ·
                refine ⟨1583953477367471017813573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33791007517172715046689557 1583953477367471017813573)
                ·
                  refine ⟨296991277006400815840045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583953477367471017813573 296991277006400815840045)
                  ·
                    rfl

theorem cell20_650687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_650687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650687 prefixEnd_650687 := by exact prefixLift 650687
  have htrace : WordTrace (prefixWord ++ tailWord_650687) baseStart_650687 baseEnd_650687 := by
    simpa [prefixWord, tailWord_650687, baseEnd_650687] using wordTrace_append hprefix tailTrace_650687
  have hstable : (prefixWord ++ tailWord_650687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650687).length < 2 ^ (prefixWord ++ tailWord_650687).sum := by decide
  have hdescent : baseEnd_650687 < baseStart_650687 := by decide
  rcases family_descends (prefixWord ++ tailWord_650687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650717 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 2]
def baseStart_650717 : Nat := 118140960795 + 650717 * 2 ^ 59
def prefixEnd_650717 : Nat := 4983230072969 + 3 ^ 40 * 650717 * 2
def baseEnd_650717 : Nat := 297004969823854044839923

theorem tailTrace_650717 : CollatzResearch.WordTrace tailWord_650717 prefixEnd_650717 297004969823854044839923 := by
  unfold tailWord_650717
  simp only [CollatzResearch.WordTrace]
  refine ⟨23733598783570917460910405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822399189047278307273603 23733598783570917460910405)
  ·
    refine ⟨4450049771919547023920701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23733598783570917460910405 4450049771919547023920701)
    ·
      refine ⟨1668768664469830133970263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4450049771919547023920701 1668768664469830133970263)
      ·
        refine ⟨2503152996704745200955395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668768664469830133970263 2503152996704745200955395)
        ·
          refine ⟨3754729495057117801433093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503152996704745200955395 3754729495057117801433093)
          ·
            refine ⟨704011780323209587768705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3754729495057117801433093 704011780323209587768705)
            ·
              refine ⟨528008835242407190826529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704011780323209587768705 528008835242407190826529)
              ·
                refine ⟨396006626431805393119897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528008835242407190826529 396006626431805393119897)
                ·
                  refine ⟨297004969823854044839923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396006626431805393119897 297004969823854044839923)
                  ·
                    rfl

theorem cell20_650717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_650717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650717 prefixEnd_650717 := by exact prefixLift 650717
  have htrace : WordTrace (prefixWord ++ tailWord_650717) baseStart_650717 baseEnd_650717 := by
    simpa [prefixWord, tailWord_650717, baseEnd_650717] using wordTrace_append hprefix tailTrace_650717
  have hstable : (prefixWord ++ tailWord_650717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650717).length < 2 ^ (prefixWord ++ tailWord_650717).sum := by decide
  have hdescent : baseEnd_650717 < baseStart_650717 := by decide
  rcases family_descends (prefixWord ++ tailWord_650717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650721 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 2]
def baseStart_650721 : Nat := 118140960795 + 650721 * 2 ^ 59
def prefixEnd_650721 : Nat := 4983230072969 + 3 ^ 40 * 650721 * 2
def baseEnd_650721 : Nat := 297006795532847808706573

theorem tailTrace_650721 : CollatzResearch.WordTrace tailWord_650721 prefixEnd_650721 297006795532847808706573 := by
  unfold tailWord_650721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23733744675556426144056017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822496450370950762704011 23733744675556426144056017)
  ·
    refine ⟨17800308506667319608042013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23733744675556426144056017 17800308506667319608042013)
    ·
      refine ⟨6675115690000244853015755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17800308506667319608042013 6675115690000244853015755)
      ·
        refine ⟨10012673535000367279523633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675115690000244853015755 10012673535000367279523633)
        ·
          refine ⟨7509505151250275459642725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10012673535000367279523633 7509505151250275459642725)
          ·
            refine ⟨1408032215859426648683011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7509505151250275459642725 1408032215859426648683011)
            ·
              refine ⟨2112048323789139973024517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408032215859426648683011 2112048323789139973024517)
              ·
                refine ⟨396009060710463744942097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2112048323789139973024517 396009060710463744942097)
                ·
                  refine ⟨297006795532847808706573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396009060710463744942097 297006795532847808706573)
                  ·
                    rfl

theorem cell20_650721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_650721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650721 prefixEnd_650721 := by exact prefixLift 650721
  have htrace : WordTrace (prefixWord ++ tailWord_650721) baseStart_650721 baseEnd_650721 := by
    simpa [prefixWord, tailWord_650721, baseEnd_650721] using wordTrace_append hprefix tailTrace_650721
  have hstable : (prefixWord ++ tailWord_650721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650721).length < 2 ^ (prefixWord ++ tailWord_650721).sum := by decide
  have hdescent : baseEnd_650721 < baseStart_650721 := by decide
  rcases family_descends (prefixWord ++ tailWord_650721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650732 : List Nat := [2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_650732 : Nat := 118140960795 + 650732 * 2 ^ 59
def prefixEnd_650732 : Nat := 4983230072969 + 3 ^ 40 * 650732 * 2
def baseEnd_650732 : Nat := 99003938744193553113287

theorem tailTrace_650732 : CollatzResearch.WordTrace tailWord_650732 prefixEnd_650732 99003938744193553113287 := by
  unfold tailWord_650732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867072939258287511353225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15822763919011050015137633 11867072939258287511353225)
  ·
    refine ⟨8900304704443715633514919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11867072939258287511353225 8900304704443715633514919)
    ·
      refine ⟨13350457056665573450272379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8900304704443715633514919 13350457056665573450272379)
      ·
        refine ⟨20025685584998360175408569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350457056665573450272379 20025685584998360175408569)
        ·
          refine ⟨15019264188748770131556427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20025685584998360175408569 15019264188748770131556427)
          ·
            refine ⟨22528896283123155197334641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15019264188748770131556427 22528896283123155197334641)
            ·
              refine ⟨16896672212342366398000981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22528896283123155197334641 16896672212342366398000981)
              ·
                refine ⟨99003938744193553113287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16896672212342366398000981 99003938744193553113287)
                ·
                  rfl

theorem cell20_650732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_650732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650732 prefixEnd_650732 := by exact prefixLift 650732
  have htrace : WordTrace (prefixWord ++ tailWord_650732) baseStart_650732 baseEnd_650732 := by
    simpa [prefixWord, tailWord_650732, baseEnd_650732] using wordTrace_append hprefix tailTrace_650732
  have hstable : (prefixWord ++ tailWord_650732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650732).length < 2 ^ (prefixWord ++ tailWord_650732).sum := by decide
  have hdescent : baseEnd_650732 < baseStart_650732 := by decide
  rcases family_descends (prefixWord ++ tailWord_650732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650742 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_650742 : Nat := 118140960795 + 650742 * 2 ^ 59
def prefixEnd_650742 : Nat := 4983230072969 + 3 ^ 40 * 650742 * 2
def baseEnd_650742 : Nat := 297016380505065069006487

theorem tailTrace_650742 : CollatzResearch.WordTrace tailWord_650742 prefixEnd_650742 297016380505065069006487 := by
  unfold tailWord_650742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483406913030021670660655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15823007072320231153713653 1483406913030021670660655)
  ·
    refine ⟨2225110369545032505990983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1483406913030021670660655 2225110369545032505990983)
    ·
      refine ⟨3337665554317548758986475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225110369545032505990983 3337665554317548758986475)
      ·
        refine ⟨5006498331476323138479713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337665554317548758986475 5006498331476323138479713)
        ·
          refine ⟨3754873748607242353859785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5006498331476323138479713 3754873748607242353859785)
          ·
            refine ⟨2816155311455431765394839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754873748607242353859785 2816155311455431765394839)
            ·
              refine ⟨4224232967183147648092259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816155311455431765394839 4224232967183147648092259)
              ·
                refine ⟨6336349450774721472138389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224232967183147648092259 6336349450774721472138389)
                ·
                  refine ⟨297016380505065069006487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6336349450774721472138389 297016380505065069006487)
                  ·
                    rfl

theorem cell20_650742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_650742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650742 prefixEnd_650742 := by exact prefixLift 650742
  have htrace : WordTrace (prefixWord ++ tailWord_650742) baseStart_650742 baseEnd_650742 := by
    simpa [prefixWord, tailWord_650742, baseEnd_650742] using wordTrace_append hprefix tailTrace_650742
  have hstable : (prefixWord ++ tailWord_650742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650742).length < 2 ^ (prefixWord ++ tailWord_650742).sum := by decide
  have hdescent : baseEnd_650742 < baseStart_650742 := by decide
  rcases family_descends (prefixWord ++ tailWord_650742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650759 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 2]
def baseStart_650759 : Nat := 118140960795 + 650759 * 2 ^ 59
def prefixEnd_650759 : Nat := 4983230072969 + 3 ^ 40 * 650759 * 2
def baseEnd_650759 : Nat := 297024139768288565439751

theorem tailTrace_650759 : CollatzResearch.WordTrace tailWord_650759 prefixEnd_650759 297024139768288565439751 := by
  unfold tailWord_650759
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735130649418758633939331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15823420432945839089292887 23735130649418758633939331)
  ·
    refine ⟨35602695974128137950908997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735130649418758633939331 35602695974128137950908997)
    ·
      refine ⟨6675505495149025865795437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35602695974128137950908997 6675505495149025865795437)
      ·
        refine ⟨2503314560680884699673289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6675505495149025865795437 2503314560680884699673289)
        ·
          refine ⟨1877485920510663524754967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503314560680884699673289 1877485920510663524754967)
          ·
            refine ⟨2816228880765995287132451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877485920510663524754967 2816228880765995287132451)
            ·
              refine ⟨4224343321148992930698677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816228880765995287132451 4224343321148992930698677)
              ·
                refine ⟨396032186357718087253001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4224343321148992930698677 396032186357718087253001)
                ·
                  refine ⟨297024139768288565439751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396032186357718087253001 297024139768288565439751)
                  ·
                    rfl

theorem cell20_650759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2].length) (baseStart_650759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650759 prefixEnd_650759 := by exact prefixLift 650759
  have htrace : WordTrace (prefixWord ++ tailWord_650759) baseStart_650759 baseEnd_650759 := by
    simpa [prefixWord, tailWord_650759, baseEnd_650759] using wordTrace_append hprefix tailTrace_650759
  have hstable : (prefixWord ++ tailWord_650759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650759).length < 2 ^ (prefixWord ++ tailWord_650759).sum := by decide
  have hdescent : baseEnd_650759 < baseStart_650759 := by decide
  rcases family_descends (prefixWord ++ tailWord_650759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650765 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 3]
def baseStart_650765 : Nat := 118140960795 + 650765 * 2 ^ 59
def prefixEnd_650765 : Nat := 4983230072969 + 3 ^ 40 * 650765 * 2
def baseEnd_650765 : Nat := 297026878331779211239727

theorem tailTrace_650765 : CollatzResearch.WordTrace tailWord_650765 prefixEnd_650765 297026878331779211239727 := by
  unfold tailWord_650765
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735349487397021658657749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15823566324931347772438499 23735349487397021658657749)
  ·
    refine ⟨556297253610867695124791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23735349487397021658657749 556297253610867695124791)
    ·
      refine ⟨834445880416301542687187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556297253610867695124791 834445880416301542687187)
      ·
        refine ⟨1251668820624452314030781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834445880416301542687187 1251668820624452314030781)
        ·
          refine ⟨469375807734169617761543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1251668820624452314030781 469375807734169617761543)
          ·
            refine ⟨704063711601254426642315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469375807734169617761543 704063711601254426642315)
            ·
              refine ⟨1056095567401881639963473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704063711601254426642315 1056095567401881639963473)
              ·
                refine ⟨792071675551411229972605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056095567401881639963473 792071675551411229972605)
                ·
                  refine ⟨297026878331779211239727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792071675551411229972605 297026878331779211239727)
                  ·
                    rfl

theorem cell20_650765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_650765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650765 prefixEnd_650765 := by exact prefixLift 650765
  have htrace : WordTrace (prefixWord ++ tailWord_650765) baseStart_650765 baseEnd_650765 := by
    simpa [prefixWord, tailWord_650765, baseEnd_650765] using wordTrace_append hprefix tailTrace_650765
  have hstable : (prefixWord ++ tailWord_650765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650765).length < 2 ^ (prefixWord ++ tailWord_650765).sum := by decide
  have hdescent : baseEnd_650765 < baseStart_650765 := by decide
  rcases family_descends (prefixWord ++ tailWord_650765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650773 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_650773 : Nat := 118140960795 + 650773 * 2 ^ 59
def prefixEnd_650773 : Nat := 4983230072969 + 3 ^ 40 * 650773 * 2
def baseEnd_650773 : Nat := 297030529749766738973027

theorem tailTrace_650773 : CollatzResearch.WordTrace tailWord_650773 prefixEnd_650773 297030529749766738973027 := by
  unfold tailWord_650773
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735641271368039024948973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15823760847578692683299315 23735641271368039024948973)
  ·
    refine ⟨8900865476763014634355865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23735641271368039024948973 8900865476763014634355865)
    ·
      refine ⟨6675649107572260975766899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8900865476763014634355865 6675649107572260975766899)
      ·
        refine ⟨10013473661358391463650349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675649107572260975766899 10013473661358391463650349)
        ·
          refine ⟨3755052623009396798868881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10013473661358391463650349 3755052623009396798868881)
          ·
            refine ⟨2816289467257047599151661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3755052623009396798868881 2816289467257047599151661)
            ·
              refine ⟨1056108550221392849681873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2816289467257047599151661 1056108550221392849681873)
              ·
                refine ⟨792081412666044637261405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056108550221392849681873 792081412666044637261405)
                ·
                  refine ⟨297030529749766738973027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792081412666044637261405 297030529749766738973027)
                  ·
                    rfl

theorem cell20_650773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_650773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650773 prefixEnd_650773 := by exact prefixLift 650773
  have htrace : WordTrace (prefixWord ++ tailWord_650773) baseStart_650773 baseEnd_650773 := by
    simpa [prefixWord, tailWord_650773, baseEnd_650773] using wordTrace_append hprefix tailTrace_650773
  have hstable : (prefixWord ++ tailWord_650773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650773).length < 2 ^ (prefixWord ++ tailWord_650773).sum := by decide
  have hdescent : baseEnd_650773 < baseStart_650773 := by decide
  rcases family_descends (prefixWord ++ tailWord_650773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650780 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_650780 : Nat := 118140960795 + 650780 * 2 ^ 59
def prefixEnd_650780 : Nat := 4983230072969 + 3 ^ 40 * 650780 * 2
def baseEnd_650780 : Nat := 297033724740505825739665

theorem tailTrace_650780 : CollatzResearch.WordTrace tailWord_650780 prefixEnd_650780 297033724740505825739665 := by
  unfold tailWord_650780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867948291171339610226897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15823931054895119480302529 11867948291171339610226897)
  ·
    refine ⟨8900961218378504707670173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11867948291171339610226897 8900961218378504707670173)
    ·
      refine ⟨3337860456891939265376315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8900961218378504707670173 3337860456891939265376315)
      ·
        refine ⟨5006790685337908898064473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337860456891939265376315 5006790685337908898064473)
        ·
          refine ⟨3755093014003431673548355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5006790685337908898064473 3755093014003431673548355)
          ·
            refine ⟨5632639521005147510322533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755093014003431673548355 5632639521005147510322533)
            ·
              refine ⟨1056119910188465158185475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5632639521005147510322533 1056119910188465158185475)
              ·
                refine ⟨1584179865282697737278213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056119910188465158185475 1584179865282697737278213)
                ·
                  refine ⟨297033724740505825739665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584179865282697737278213 297033724740505825739665)
                  ·
                    rfl

theorem cell20_650780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_650780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650780 prefixEnd_650780 := by exact prefixLift 650780
  have htrace : WordTrace (prefixWord ++ tailWord_650780) baseStart_650780 baseEnd_650780 := by
    simpa [prefixWord, tailWord_650780, baseEnd_650780] using wordTrace_append hprefix tailTrace_650780
  have hstable : (prefixWord ++ tailWord_650780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650780).length < 2 ^ (prefixWord ++ tailWord_650780).sum := by decide
  have hdescent : baseEnd_650780 < baseStart_650780 := by decide
  rcases family_descends (prefixWord ++ tailWord_650780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650832 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_650832 : Nat := 118140960795 + 650832 * 2 ^ 59
def prefixEnd_650832 : Nat := 4983230072969 + 3 ^ 40 * 650832 * 2
def baseEnd_650832 : Nat := 297057458957424756006119

theorem tailTrace_650832 : CollatzResearch.WordTrace tailWord_650832 prefixEnd_650832 297057458957424756006119 := by
  unfold tailWord_650832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868896589077146050673375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15825195452102861400897833 11868896589077146050673375)
  ·
    refine ⟨17803344883615719076010063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11868896589077146050673375 17803344883615719076010063)
    ·
      refine ⟨26705017325423578614015095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17803344883615719076010063 26705017325423578614015095)
      ·
        refine ⟨40057525988135367921022643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26705017325423578614015095 40057525988135367921022643)
        ·
          refine ⟨60086288982203051881533965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40057525988135367921022643 60086288982203051881533965)
          ·
            refine ⟨22532358368326144455575237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60086288982203051881533965 22532358368326144455575237)
            ·
              refine ⟨4224817194061152085420357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22532358368326144455575237 4224817194061152085420357)
              ·
                refine ⟨792153223886466016016317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4224817194061152085420357 792153223886466016016317)
                ·
                  refine ⟨297057458957424756006119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792153223886466016016317 297057458957424756006119)
                  ·
                    rfl

theorem cell20_650832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_650832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650832 prefixEnd_650832 := by exact prefixLift 650832
  have htrace : WordTrace (prefixWord ++ tailWord_650832) baseStart_650832 baseEnd_650832 := by
    simpa [prefixWord, tailWord_650832, baseEnd_650832] using wordTrace_append hprefix tailTrace_650832
  have hstable : (prefixWord ++ tailWord_650832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650832).length < 2 ^ (prefixWord ++ tailWord_650832).sum := by decide
  have hdescent : baseEnd_650832 < baseStart_650832 := by decide
  rcases family_descends (prefixWord ++ tailWord_650832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650838 : List Nat := [5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_650838 : Nat := 118140960795 + 650838 * 2 ^ 59
def prefixEnd_650838 : Nat := 4983230072969 + 3 ^ 40 * 650838 * 2
def baseEnd_650838 : Nat := 99020065840305133935365

theorem tailTrace_650838 : CollatzResearch.WordTrace tailWord_650838 prefixEnd_650838 99020065840305133935365 := by
  unfold tailWord_650838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483625751008284695379073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15825341344088370084043445 1483625751008284695379073)
  ·
    refine ⟨1112719313256213521534305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483625751008284695379073 1112719313256213521534305)
    ·
      refine ⟨834539484942160141150729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1112719313256213521534305 834539484942160141150729)
      ·
        refine ⟨625904613706620105863047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834539484942160141150729 625904613706620105863047)
        ·
          refine ⟨938856920559930158794571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625904613706620105863047 938856920559930158794571)
          ·
            refine ⟨1408285380839895238191857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938856920559930158794571 1408285380839895238191857)
            ·
              refine ⟨1056214035629921428643893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408285380839895238191857 1056214035629921428643893)
              ·
                refine ⟨99020065840305133935365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1056214035629921428643893 99020065840305133935365)
                ·
                  rfl

theorem cell20_650838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_650838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650838 prefixEnd_650838 := by exact prefixLift 650838
  have htrace : WordTrace (prefixWord ++ tailWord_650838) baseStart_650838 baseEnd_650838 := by
    simpa [prefixWord, tailWord_650838, baseEnd_650838] using wordTrace_append hprefix tailTrace_650838
  have hstable : (prefixWord ++ tailWord_650838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650838).length < 2 ^ (prefixWord ++ tailWord_650838).sum := by decide
  have hdescent : baseEnd_650838 < baseStart_650838 := by decide
  rcases family_descends (prefixWord ++ tailWord_650838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650845 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_650845 : Nat := 118140960795 + 650845 * 2 ^ 59
def prefixEnd_650845 : Nat := 4983230072969 + 3 ^ 40 * 650845 * 2
def baseEnd_650845 : Nat := 297063392511654488572733

theorem tailTrace_650845 : CollatzResearch.WordTrace tailWord_650845 prefixEnd_650845 297063392511654488572733 := by
  unfold tailWord_650845
  simp only [CollatzResearch.WordTrace]
  refine ⟨23738267327107195321569989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15825511551404796881046659 23738267327107195321569989)
  ·
    refine ⟨4450925123832599122794373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23738267327107195321569989 4450925123832599122794373)
    ·
      refine ⟨834548460718612335523945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4450925123832599122794373 834548460718612335523945)
      ·
        refine ⟨625911345538959251642959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834548460718612335523945 625911345538959251642959)
        ·
          refine ⟨938867018308438877464439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625911345538959251642959 938867018308438877464439)
          ·
            refine ⟨1408300527462658316196659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938867018308438877464439 1408300527462658316196659)
            ·
              refine ⟨2112450791193987474294989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408300527462658316196659 2112450791193987474294989)
              ·
                refine ⟨792169046697745302860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2112450791193987474294989 792169046697745302860621)
                ·
                  refine ⟨297063392511654488572733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792169046697745302860621 297063392511654488572733)
                  ·
                    rfl

theorem cell20_650845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_650845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650845 prefixEnd_650845 := by exact prefixLift 650845
  have htrace : WordTrace (prefixWord ++ tailWord_650845) baseStart_650845 baseEnd_650845 := by
    simpa [prefixWord, tailWord_650845, baseEnd_650845] using wordTrace_append hprefix tailTrace_650845
  have hstable : (prefixWord ++ tailWord_650845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650845).length < 2 ^ (prefixWord ++ tailWord_650845).sum := by decide
  have hdescent : baseEnd_650845 < baseStart_650845 := by decide
  rcases family_descends (prefixWord ++ tailWord_650845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650884 : List Nat := [2, 3, 2, 1, 12]
def baseStart_650884 : Nat := 118140960795 + 650884 * 2 ^ 59
def prefixEnd_650884 : Nat := 4983230072969 + 3 ^ 40 * 650884 * 2
def baseEnd_650884 : Nat := 3667669051535107237933

theorem tailTrace_650884 : CollatzResearch.WordTrace tailWord_650884 prefixEnd_650884 3667669051535107237933 := by
  unfold tailWord_650884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869844886982952491119853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15826459849310603321493137 11869844886982952491119853)
  ·
    refine ⟨4451191832618607184169945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11869844886982952491119853 4451191832618607184169945)
    ·
      refine ⟨3338393874463955388127459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4451191832618607184169945 3338393874463955388127459)
      ·
        refine ⟨5007590811695933082191189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338393874463955388127459 5007590811695933082191189)
        ·
          refine ⟨3667669051535107237933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5007590811695933082191189 3667669051535107237933)
          ·
            rfl

theorem cell20_650884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 12].length) (baseStart_650884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650884 prefixEnd_650884 := by exact prefixLift 650884
  have htrace : WordTrace (prefixWord ++ tailWord_650884) baseStart_650884 baseEnd_650884 := by
    simpa [prefixWord, tailWord_650884, baseEnd_650884] using wordTrace_append hprefix tailTrace_650884
  have hstable : (prefixWord ++ tailWord_650884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650884).length < 2 ^ (prefixWord ++ tailWord_650884).sum := by decide
  have hdescent : baseEnd_650884 < baseStart_650884 := by decide
  rcases family_descends (prefixWord ++ tailWord_650884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650887 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_650887 : Nat := 118140960795 + 650887 * 2 ^ 59
def prefixEnd_650887 : Nat := 4983230072969 + 3 ^ 40 * 650887 * 2
def baseEnd_650887 : Nat := 297082562456089009172561

theorem tailTrace_650887 : CollatzResearch.WordTrace tailWord_650887 prefixEnd_650887 297082562456089009172561 := by
  unfold tailWord_650887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739799192955036494598915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15826532795303357663065943 23739799192955036494598915)
  ·
    refine ⟨35609698789432554741898373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23739799192955036494598915 35609698789432554741898373)
    ·
      refine ⟨6676818523018604014105945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35609698789432554741898373 6676818523018604014105945)
      ·
        refine ⟨5007613892263953010579459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6676818523018604014105945 5007613892263953010579459)
        ·
          refine ⟨7511420838395929515869189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007613892263953010579459 7511420838395929515869189)
          ·
            refine ⟨1408391407199236784225473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7511420838395929515869189 1408391407199236784225473)
            ·
              refine ⟨1056293555399427588169105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408391407199236784225473 1056293555399427588169105)
              ·
                refine ⟨792220166549570691126829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056293555399427588169105 792220166549570691126829)
                ·
                  refine ⟨297082562456089009172561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792220166549570691126829 297082562456089009172561)
                  ·
                    rfl

theorem cell20_650887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_650887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650887 prefixEnd_650887 := by exact prefixLift 650887
  have htrace : WordTrace (prefixWord ++ tailWord_650887) baseStart_650887 baseEnd_650887 := by
    simpa [prefixWord, tailWord_650887, baseEnd_650887] using wordTrace_append hprefix tailTrace_650887
  have hstable : (prefixWord ++ tailWord_650887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650887).length < 2 ^ (prefixWord ++ tailWord_650887).sum := by decide
  have hdescent : baseEnd_650887 < baseStart_650887 := by decide
  rcases family_descends (prefixWord ++ tailWord_650887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650890 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_650890 : Nat := 118140960795 + 650890 * 2 ^ 59
def prefixEnd_650890 : Nat := 4983230072969 + 3 ^ 40 * 650890 * 2
def baseEnd_650890 : Nat := 297083931737834332072549

theorem tailTrace_650890 : CollatzResearch.WordTrace tailWord_650890 prefixEnd_650890 297083931737834332072549 := by
  unfold tailWord_650890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934977152986042001739531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15826605741296112004638749 5934977152986042001739531)
  ·
    refine ⟨8902465729479063002609297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5934977152986042001739531 8902465729479063002609297)
    ·
      refine ⟨6676849297109297251956973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8902465729479063002609297 6676849297109297251956973)
      ·
        refine ⟨2503818486415986469483865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6676849297109297251956973 2503818486415986469483865)
        ·
          refine ⟨1877863864811989852112899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503818486415986469483865 1877863864811989852112899)
          ·
            refine ⟨2816795797217984778169349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877863864811989852112899 2816795797217984778169349)
            ·
              refine ⟨528149211978372145906753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2816795797217984778169349 528149211978372145906753)
              ·
                refine ⟨396111908983779109430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528149211978372145906753 396111908983779109430065)
                ·
                  refine ⟨297083931737834332072549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396111908983779109430065 297083931737834332072549)
                  ·
                    rfl

theorem cell20_650890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_650890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650890 prefixEnd_650890 := by exact prefixLift 650890
  have htrace : WordTrace (prefixWord ++ tailWord_650890) baseStart_650890 baseEnd_650890 := by
    simpa [prefixWord, tailWord_650890, baseEnd_650890] using wordTrace_append hprefix tailTrace_650890
  have hstable : (prefixWord ++ tailWord_650890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650890).length < 2 ^ (prefixWord ++ tailWord_650890).sum := by decide
  have hdescent : baseEnd_650890 < baseStart_650890 := by decide
  rcases family_descends (prefixWord ++ tailWord_650890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650911 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_650911 : Nat := 118140960795 + 650911 * 2 ^ 59
def prefixEnd_650911 : Nat := 4983230072969 + 3 ^ 40 * 650911 * 2
def baseEnd_650911 : Nat := 297093516710051592372463

theorem tailTrace_650911 : CollatzResearch.WordTrace tailWord_650911 prefixEnd_650911 297093516710051592372463 := by
  unfold tailWord_650911
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740674544868088593472587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15827116363245392395648391 23740674544868088593472587)
  ·
    refine ⟨35611011817302132890208881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23740674544868088593472587 35611011817302132890208881)
    ·
      refine ⟨26708258862976599667656661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35611011817302132890208881 26708258862976599667656661)
      ·
        refine ⟨625974817101014054710703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26708258862976599667656661 625974817101014054710703)
        ·
          refine ⟨938962225651521082066055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625974817101014054710703 938962225651521082066055)
          ·
            refine ⟨1408443338477281623099083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938962225651521082066055 1408443338477281623099083)
            ·
              refine ⟨2112665007715922434648625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408443338477281623099083 2112665007715922434648625)
              ·
                refine ⟨1584498755786941825986469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112665007715922434648625 1584498755786941825986469)
                ·
                  refine ⟨297093516710051592372463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584498755786941825986469 297093516710051592372463)
                  ·
                    rfl

theorem cell20_650911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_650911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650911 prefixEnd_650911 := by exact prefixLift 650911
  have htrace : WordTrace (prefixWord ++ tailWord_650911) baseStart_650911 baseEnd_650911 := by
    simpa [prefixWord, tailWord_650911, baseEnd_650911] using wordTrace_append hprefix tailTrace_650911
  have hstable : (prefixWord ++ tailWord_650911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650911).length < 2 ^ (prefixWord ++ tailWord_650911).sum := by decide
  have hdescent : baseEnd_650911 < baseStart_650911 := by decide
  rcases family_descends (prefixWord ++ tailWord_650911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650915 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_650915 : Nat := 118140960795 + 650915 * 2 ^ 59
def prefixEnd_650915 : Nat := 4983230072969 + 3 ^ 40 * 650915 * 2
def baseEnd_650915 : Nat := 297095342419045356239113

theorem tailTrace_650915 : CollatzResearch.WordTrace tailWord_650915 prefixEnd_650915 297095342419045356239113 := by
  unfold tailWord_650915
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740820436853597276618199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15827213624569064851078799 23740820436853597276618199)
  ·
    refine ⟨35611230655280395914927299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23740820436853597276618199 35611230655280395914927299)
    ·
      refine ⟨53416845982920593872390949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35611230655280395914927299 53416845982920593872390949)
      ·
        refine ⟨10015658621797611351073303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53416845982920593872390949 10015658621797611351073303)
        ·
          refine ⟨15023487932696417026609955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10015658621797611351073303 15023487932696417026609955)
          ·
            refine ⟨22535231899044625539914933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15023487932696417026609955 22535231899044625539914933)
            ·
              refine ⟨2112677990535433644367025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22535231899044625539914933 2112677990535433644367025)
              ·
                refine ⟨1584508492901575233275269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112677990535433644367025 1584508492901575233275269)
                ·
                  refine ⟨297095342419045356239113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584508492901575233275269 297095342419045356239113)
                  ·
                    rfl

theorem cell20_650915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_650915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650915 prefixEnd_650915 := by exact prefixLift 650915
  have htrace : WordTrace (prefixWord ++ tailWord_650915) baseStart_650915 baseEnd_650915 := by
    simpa [prefixWord, tailWord_650915, baseEnd_650915] using wordTrace_append hprefix tailTrace_650915
  have hstable : (prefixWord ++ tailWord_650915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650915).length < 2 ^ (prefixWord ++ tailWord_650915).sum := by decide
  have hdescent : baseEnd_650915 < baseStart_650915 := by decide
  rcases family_descends (prefixWord ++ tailWord_650915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650942 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_650942 : Nat := 118140960795 + 650942 * 2 ^ 59
def prefixEnd_650942 : Nat := 4983230072969 + 3 ^ 40 * 650942 * 2
def baseEnd_650942 : Nat := 297107665954753262339003

theorem tailTrace_650942 : CollatzResearch.WordTrace tailWord_650942 prefixEnd_650942 297107665954753262339003 := by
  unfold tailWord_650942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967725650969472610981385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15827870138503853925234053 2967725650969472610981385)
  ·
    refine ⟨2225794238227104458236039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2967725650969472610981385 2225794238227104458236039)
    ·
      refine ⟨3338691357340656687354059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225794238227104458236039 3338691357340656687354059)
      ·
        refine ⟨5008037036010985031031089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338691357340656687354059 5008037036010985031031089)
        ·
          refine ⟨3756027777008238773273317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008037036010985031031089 3756027777008238773273317)
          ·
            refine ⟨704255208189044769988747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3756027777008238773273317 704255208189044769988747)
            ·
              refine ⟨1056382812283567154983121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704255208189044769988747 1056382812283567154983121)
              ·
                refine ⟨792287109212675366237341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056382812283567154983121 792287109212675366237341)
                ·
                  refine ⟨297107665954753262339003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792287109212675366237341 297107665954753262339003)
                  ·
                    rfl

theorem cell20_650942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_650942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650942 prefixEnd_650942 := by exact prefixLift 650942
  have htrace : WordTrace (prefixWord ++ tailWord_650942) baseStart_650942 baseEnd_650942 := by
    simpa [prefixWord, tailWord_650942, baseEnd_650942] using wordTrace_append hprefix tailTrace_650942
  have hstable : (prefixWord ++ tailWord_650942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650942).length < 2 ^ (prefixWord ++ tailWord_650942).sum := by decide
  have hdescent : baseEnd_650942 < baseStart_650942 := by decide
  rcases family_descends (prefixWord ++ tailWord_650942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650977 : List Nat := [1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_650977 : Nat := 118140960795 + 650977 * 2 ^ 59
def prefixEnd_650977 : Nat := 4983230072969 + 3 ^ 40 * 650977 * 2
def baseEnd_650977 : Nat := 99041213636149565390731

theorem tailTrace_650977 : CollatzResearch.WordTrace tailWord_650977 prefixEnd_650977 99041213636149565390731 := by
  unfold tailWord_650977
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743081762628981865375185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15828721175085987910250123 23743081762628981865375185)
  ·
    refine ⟨17807311321971736399031389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23743081762628981865375185 17807311321971736399031389)
    ·
      refine ⟨6677741745739401149636771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17807311321971736399031389 6677741745739401149636771)
      ·
        refine ⟨10016612618609101724455157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677741745739401149636771 10016612618609101724455157)
        ·
          refine ⟨939057432994603286667671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10016612618609101724455157 939057432994603286667671)
          ·
            refine ⟨1408586149491904930001507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939057432994603286667671 1408586149491904930001507)
            ·
              refine ⟨2112879224237857395002261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408586149491904930001507 2112879224237857395002261)
              ·
                refine ⟨99041213636149565390731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2112879224237857395002261 99041213636149565390731)
                ·
                  rfl

theorem cell20_650977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_650977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650977 prefixEnd_650977 := by exact prefixLift 650977
  have htrace : WordTrace (prefixWord ++ tailWord_650977) baseStart_650977 baseEnd_650977 := by
    simpa [prefixWord, tailWord_650977, baseEnd_650977] using wordTrace_append hprefix tailTrace_650977
  have hstable : (prefixWord ++ tailWord_650977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650977).length < 2 ^ (prefixWord ++ tailWord_650977).sum := by decide
  have hdescent : baseEnd_650977 < baseStart_650977 := by decide
  rcases family_descends (prefixWord ++ tailWord_650977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650983 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 2]
def baseStart_650983 : Nat := 118140960795 + 650983 * 2 ^ 59
def prefixEnd_650983 : Nat := 4983230072969 + 3 ^ 40 * 650983 * 2
def baseEnd_650983 : Nat := 297126379471939341972169

theorem tailTrace_650983 : CollatzResearch.WordTrace tailWord_650983 prefixEnd_650983 297126379471939341972169 := by
  unfold tailWord_650983
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743300600607244890093603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15828867067071496593395735 23743300600607244890093603)
  ·
    refine ⟨35614950900910867335140405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743300600607244890093603 35614950900910867335140405)
    ·
      refine ⟨3338901646960393812669413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35614950900910867335140405 3338901646960393812669413)
      ·
        refine ⟨626044058805073839875515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3338901646960393812669413 626044058805073839875515)
        ·
          refine ⟨939066088207610759813273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626044058805073839875515 939066088207610759813273)
          ·
            refine ⟨704299566155708069859955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939066088207610759813273 704299566155708069859955)
            ·
              refine ⟨1056449349233562104789933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704299566155708069859955 1056449349233562104789933)
              ·
                refine ⟨396168505962585789296225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056449349233562104789933 396168505962585789296225)
                ·
                  refine ⟨297126379471939341972169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396168505962585789296225 297126379471939341972169)
                  ·
                    rfl

theorem cell20_650983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2].length) (baseStart_650983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650983 prefixEnd_650983 := by exact prefixLift 650983
  have htrace : WordTrace (prefixWord ++ tailWord_650983) baseStart_650983 baseEnd_650983 := by
    simpa [prefixWord, tailWord_650983, baseEnd_650983] using wordTrace_append hprefix tailTrace_650983
  have hstable : (prefixWord ++ tailWord_650983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650983).length < 2 ^ (prefixWord ++ tailWord_650983).sum := by decide
  have hdescent : baseEnd_650983 < baseStart_650983 := by decide
  rcases family_descends (prefixWord ++ tailWord_650983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650984 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_650984 : Nat := 118140960795 + 650984 * 2 ^ 59
def prefixEnd_650984 : Nat := 4983230072969 + 3 ^ 40 * 650984 * 2
def baseEnd_650984 : Nat := 297126835899187782938831

theorem tailTrace_650984 : CollatzResearch.WordTrace tailWord_650984 prefixEnd_650984 297126835899187782938831 := by
  unfold tailWord_650984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871668536801811030440003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15828891382402414707253337 11871668536801811030440003)
  ·
    refine ⟨17807502805202716545660005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11871668536801811030440003 17807502805202716545660005)
    ·
      refine ⟨3338906775975509352311251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17807502805202716545660005 3338906775975509352311251)
      ·
        refine ⟨5008360163963264028466877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338906775975509352311251 5008360163963264028466877)
        ·
          refine ⟨1878135061486224010675079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5008360163963264028466877 1878135061486224010675079)
          ·
            refine ⟨2817202592229336016012619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878135061486224010675079 2817202592229336016012619)
            ·
              refine ⟨4225803888344004024018929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817202592229336016012619 4225803888344004024018929)
              ·
                refine ⟨3169352916258003018014197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225803888344004024018929 3169352916258003018014197)
                ·
                  refine ⟨297126835899187782938831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3169352916258003018014197 297126835899187782938831)
                  ·
                    rfl

theorem cell20_650984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_650984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_650984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_650984 prefixEnd_650984 := by exact prefixLift 650984
  have htrace : WordTrace (prefixWord ++ tailWord_650984) baseStart_650984 baseEnd_650984 := by
    simpa [prefixWord, tailWord_650984, baseEnd_650984] using wordTrace_append hprefix tailTrace_650984
  have hstable : (prefixWord ++ tailWord_650984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650984).length < 2 ^ (prefixWord ++ tailWord_650984).sum := by decide
  have hdescent : baseEnd_650984 < baseStart_650984 := by decide
  rcases family_descends (prefixWord ++ tailWord_650984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651018 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_651018 : Nat := 118140960795 + 651018 * 2 ^ 59
def prefixEnd_651018 : Nat := 4983230072969 + 3 ^ 40 * 651018 * 2
def baseEnd_651018 : Nat := 297142354425634775805359

theorem tailTrace_651018 : CollatzResearch.WordTrace tailWord_651018 prefixEnd_651018 297142354425634775805359 := by
  unfold tailWord_651018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936144288870111466904427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15829718103653630578411805 5936144288870111466904427)
  ·
    refine ⟨8904216433305167200356641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936144288870111466904427 8904216433305167200356641)
    ·
      refine ⟨6678162324978875400267481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8904216433305167200356641 6678162324978875400267481)
      ·
        refine ⟨5008621743734156550200611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6678162324978875400267481 5008621743734156550200611)
        ·
          refine ⟨7512932615601234825300917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008621743734156550200611 7512932615601234825300917)
          ·
            refine ⟨704337432712615764871961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7512932615601234825300917 704337432712615764871961)
            ·
              refine ⟨528253074534461823653971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704337432712615764871961 528253074534461823653971)
              ·
                refine ⟨792379611801692735480957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528253074534461823653971 792379611801692735480957)
                ·
                  refine ⟨297142354425634775805359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792379611801692735480957 297142354425634775805359)
                  ·
                    rfl

theorem cell20_651018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_651018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651018 prefixEnd_651018 := by exact prefixLift 651018
  have htrace : WordTrace (prefixWord ++ tailWord_651018) baseStart_651018 baseEnd_651018 := by
    simpa [prefixWord, tailWord_651018, baseEnd_651018] using wordTrace_append hprefix tailTrace_651018
  have hstable : (prefixWord ++ tailWord_651018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651018).length < 2 ^ (prefixWord ++ tailWord_651018).sum := by decide
  have hdescent : baseEnd_651018 < baseStart_651018 := by decide
  rcases family_descends (prefixWord ++ tailWord_651018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651036 : List Nat := [2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_651036 : Nat := 118140960795 + 651036 * 2 ^ 59
def prefixEnd_651036 : Nat := 4983230072969 + 3 ^ 40 * 651036 * 2
def baseEnd_651036 : Nat := 99050190038702237735095

theorem tailTrace_651036 : CollatzResearch.WordTrace tailWord_651036 prefixEnd_651036 99050190038702237735095 := by
  unfold tailWord_651036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872616834707617470886481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15830155779610156627848641 11872616834707617470886481)
  ·
    refine ⟨8904462626030713103164861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11872616834707617470886481 8904462626030713103164861)
    ·
      refine ⟨3339173484761517413686823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8904462626030713103164861 3339173484761517413686823)
      ·
        refine ⟨5008760227142276120530235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339173484761517413686823 5008760227142276120530235)
        ·
          refine ⟨7513140340713414180795353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008760227142276120530235 7513140340713414180795353)
          ·
            refine ⟨5634855255535060635596515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7513140340713414180795353 5634855255535060635596515)
            ·
              refine ⟨8452282883302590953394773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634855255535060635596515 8452282883302590953394773)
              ·
                refine ⟨99050190038702237735095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8452282883302590953394773 99050190038702237735095)
                ·
                  rfl

theorem cell20_651036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_651036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651036 prefixEnd_651036 := by exact prefixLift 651036
  have htrace : WordTrace (prefixWord ++ tailWord_651036) baseStart_651036 baseEnd_651036 := by
    simpa [prefixWord, tailWord_651036, baseEnd_651036] using wordTrace_append hprefix tailTrace_651036
  have hstable : (prefixWord ++ tailWord_651036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651036).length < 2 ^ (prefixWord ++ tailWord_651036).sum := by decide
  have hdescent : baseEnd_651036 < baseStart_651036 := by decide
  rcases family_descends (prefixWord ++ tailWord_651036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651043 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_651043 : Nat := 118140960795 + 651043 * 2 ^ 59
def prefixEnd_651043 : Nat := 4983230072969 + 3 ^ 40 * 651043 * 2
def baseEnd_651043 : Nat := 297153765106845799971923

theorem tailTrace_651043 : CollatzResearch.WordTrace tailWord_651043 prefixEnd_651043 297153765106845799971923 := by
  unfold tailWord_651043
  simp only [CollatzResearch.WordTrace]
  refine ⟨23745488980389875137277783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15830325986926583424851855 23745488980389875137277783)
  ·
    refine ⟨35618233470584812705916675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23745488980389875137277783 35618233470584812705916675)
    ·
      refine ⟨53427350205877219058875013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35618233470584812705916675 53427350205877219058875013)
      ·
        refine ⟨10017628163601978573539065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53427350205877219058875013 10017628163601978573539065)
        ·
          refine ⟨7513221122701483930154299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10017628163601978573539065 7513221122701483930154299)
          ·
            refine ⟨11269831684052225895231449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7513221122701483930154299 11269831684052225895231449)
            ·
              refine ⟨8452373763039169421423587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11269831684052225895231449 8452373763039169421423587)
              ·
                refine ⟨12678560644558754132135381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8452373763039169421423587 12678560644558754132135381)
                ·
                  refine ⟨297153765106845799971923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12678560644558754132135381 297153765106845799971923)
                  ·
                    rfl

theorem cell20_651043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_651043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651043 prefixEnd_651043 := by exact prefixLift 651043
  have htrace : WordTrace (prefixWord ++ tailWord_651043) baseStart_651043 baseEnd_651043 := by
    simpa [prefixWord, tailWord_651043, baseEnd_651043] using wordTrace_append hprefix tailTrace_651043
  have hstable : (prefixWord ++ tailWord_651043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651043).length < 2 ^ (prefixWord ++ tailWord_651043).sum := by decide
  have hdescent : baseEnd_651043 < baseStart_651043 := by decide
  rcases family_descends (prefixWord ++ tailWord_651043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651059 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 2]
def baseStart_651059 : Nat := 118140960795 + 651059 * 2 ^ 59
def prefixEnd_651059 : Nat := 4983230072969 + 3 ^ 40 * 651059 * 2
def baseEnd_651059 : Nat := 297161067942820855438525

theorem tailTrace_651059 : CollatzResearch.WordTrace tailWord_651059 prefixEnd_651059 297161067942820855438525 := by
  unfold tailWord_651059
  simp only [CollatzResearch.WordTrace]
  refine ⟨23746072548331909869860231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15830715032221273246573487 23746072548331909869860231)
  ·
    refine ⟨35619108822497864804790347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23746072548331909869860231 35619108822497864804790347)
    ·
      refine ⟨53428663233746797207185521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35619108822497864804790347 53428663233746797207185521)
      ·
        refine ⟨40071497425310097905389141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53428663233746797207185521 40071497425310097905389141)
        ·
          refine ⟨469587860452852709828779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 40071497425310097905389141 469587860452852709828779)
          ·
            refine ⟨704381790679279064743169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469587860452852709828779 704381790679279064743169)
            ·
              refine ⟨528286343009459298557377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704381790679279064743169 528286343009459298557377)
              ·
                refine ⟨396214757257094473918033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528286343009459298557377 396214757257094473918033)
                ·
                  refine ⟨297161067942820855438525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396214757257094473918033 297161067942820855438525)
                  ·
                    rfl

theorem cell20_651059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2].length) (baseStart_651059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651059 prefixEnd_651059 := by exact prefixLift 651059
  have htrace : WordTrace (prefixWord ++ tailWord_651059) baseStart_651059 baseEnd_651059 := by
    simpa [prefixWord, tailWord_651059, baseEnd_651059] using wordTrace_append hprefix tailTrace_651059
  have hstable : (prefixWord ++ tailWord_651059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651059).length < 2 ^ (prefixWord ++ tailWord_651059).sum := by decide
  have hdescent : baseEnd_651059 < baseStart_651059 := by decide
  rcases family_descends (prefixWord ++ tailWord_651059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651070 : List Nat := [4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_651070 : Nat := 118140960795 + 651070 * 2 ^ 59
def prefixEnd_651070 : Nat := 4983230072969 + 3 ^ 40 * 651070 * 2
def baseEnd_651070 : Nat := 99055362880851235357271

theorem tailTrace_651070 : CollatzResearch.WordTrace tailWord_651070 prefixEnd_651070 99055362880851235357271 := by
  unfold tailWord_651070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968309218911507343563833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15830982500861372499007109 2968309218911507343563833)
  ·
    refine ⟨2226231914183630507672875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2968309218911507343563833 2226231914183630507672875)
    ·
      refine ⟨3339347871275445761509313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226231914183630507672875 3339347871275445761509313)
      ·
        refine ⟨2504510903456584321131985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339347871275445761509313 2504510903456584321131985)
        ·
          refine ⟨1878383177592438240848989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504510903456584321131985 1878383177592438240848989)
          ·
            refine ⟨704393691597164340318371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1878383177592438240848989 704393691597164340318371)
            ·
              refine ⟨1056590537395746510477557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704393691597164340318371 1056590537395746510477557)
              ·
                refine ⟨99055362880851235357271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1056590537395746510477557 99055362880851235357271)
                ·
                  rfl

theorem cell20_651070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_651070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651070 prefixEnd_651070 := by exact prefixLift 651070
  have htrace : WordTrace (prefixWord ++ tailWord_651070) baseStart_651070 baseEnd_651070 := by
    simpa [prefixWord, tailWord_651070, baseEnd_651070] using wordTrace_append hprefix tailTrace_651070
  have hstable : (prefixWord ++ tailWord_651070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651070).length < 2 ^ (prefixWord ++ tailWord_651070).sum := by decide
  have hdescent : baseEnd_651070 < baseStart_651070 := by decide
  rcases family_descends (prefixWord ++ tailWord_651070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651084 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_651084 : Nat := 118140960795 + 651084 * 2 ^ 59
def prefixEnd_651084 : Nat := 4983230072969 + 3 ^ 40 * 651084 * 2
def baseEnd_651084 : Nat := 297172478624031879605089

theorem tailTrace_651084 : CollatzResearch.WordTrace tailWord_651084 prefixEnd_651084 297172478624031879605089 := by
  unfold tailWord_651084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873492186620669569760153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15831322915494226093013537 11873492186620669569760153)
  ·
    refine ⟨8905119139965502177320115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11873492186620669569760153 8905119139965502177320115)
    ·
      refine ⟨13357678709948253265980173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8905119139965502177320115 13357678709948253265980173)
      ·
        refine ⟨5009129516230594974742565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13357678709948253265980173 5009129516230594974742565)
        ·
          refine ⟨939211784293236557764231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5009129516230594974742565 939211784293236557764231)
          ·
            refine ⟨1408817676439854836646347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939211784293236557764231 1408817676439854836646347)
            ·
              refine ⟨2113226514659782254969521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408817676439854836646347 2113226514659782254969521)
              ·
                refine ⟨1584919885994836691227141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113226514659782254969521 1584919885994836691227141)
                ·
                  refine ⟨297172478624031879605089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584919885994836691227141 297172478624031879605089)
                  ·
                    rfl

theorem cell20_651084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_651084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651084 prefixEnd_651084 := by exact prefixLift 651084
  have htrace : WordTrace (prefixWord ++ tailWord_651084) baseStart_651084 baseEnd_651084 := by
    simpa [prefixWord, tailWord_651084, baseEnd_651084] using wordTrace_append hprefix tailTrace_651084
  have hstable : (prefixWord ++ tailWord_651084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651084).length < 2 ^ (prefixWord ++ tailWord_651084).sum := by decide
  have hdescent : baseEnd_651084 < baseStart_651084 := by decide
  rcases family_descends (prefixWord ++ tailWord_651084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651112 : List Nat := [2, 1, 4, 2, 1, 1, 9]
def baseStart_651112 : Nat := 118140960795 + 651112 * 2 ^ 59
def prefixEnd_651112 : Nat := 4983230072969 + 3 ^ 40 * 651112 * 2
def baseEnd_651112 : Nat := 33020584287443136296849

theorem tailTrace_651112 : CollatzResearch.WordTrace tailWord_651112 prefixEnd_651112 33020584287443136296849 := by
  unfold tailWord_651112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874002808569949960769795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15832003744759933281026393 11874002808569949960769795)
  ·
    refine ⟨17811004212854924941154693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11874002808569949960769795 17811004212854924941154693)
    ·
      refine ⟨3339563289910298426466505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17811004212854924941154693 3339563289910298426466505)
      ·
        refine ⟨2504672467432723819849879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339563289910298426466505 2504672467432723819849879)
        ·
          refine ⟨3757008701149085729774819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504672467432723819849879 3757008701149085729774819)
          ·
            refine ⟨5635513051723628594662229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757008701149085729774819 5635513051723628594662229)
            ·
              refine ⟨33020584287443136296849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5635513051723628594662229 33020584287443136296849)
              ·
                rfl

theorem cell20_651112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_651112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651112 prefixEnd_651112 := by exact prefixLift 651112
  have htrace : WordTrace (prefixWord ++ tailWord_651112) baseStart_651112 baseEnd_651112 := by
    simpa [prefixWord, tailWord_651112, baseEnd_651112] using wordTrace_append hprefix tailTrace_651112
  have hstable : (prefixWord ++ tailWord_651112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651112).length < 2 ^ (prefixWord ++ tailWord_651112).sum := by decide
  have hdescent : baseEnd_651112 < baseStart_651112 := by decide
  rcases family_descends (prefixWord ++ tailWord_651112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651156 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_651156 : Nat := 118140960795 + 651156 * 2 ^ 59
def prefixEnd_651156 : Nat := 4983230072969 + 3 ^ 40 * 651156 * 2
def baseEnd_651156 : Nat := 297205341385919629204795

theorem tailTrace_651156 : CollatzResearch.WordTrace tailWord_651156 prefixEnd_651156 297205341385919629204795 := by
  unfold tailWord_651156
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874805214490247718070661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15833073619320330290760881 11874805214490247718070661)
  ·
    refine ⟨2226525977716921447138249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11874805214490247718070661 2226525977716921447138249)
    ·
      refine ⟨1669894483287691085353687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2226525977716921447138249 1669894483287691085353687)
      ·
        refine ⟨2504841724931536628030531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669894483287691085353687 2504841724931536628030531)
        ·
          refine ⟨3757262587397304942045797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504841724931536628030531 3757262587397304942045797)
          ·
            refine ⟨704486735136994676633587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3757262587397304942045797 704486735136994676633587)
            ·
              refine ⟨1056730102705492014950381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704486735136994676633587 1056730102705492014950381)
              ·
                refine ⟨396273788514559505606393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056730102705492014950381 396273788514559505606393)
                ·
                  refine ⟨297205341385919629204795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396273788514559505606393 297205341385919629204795)
                  ·
                    rfl

theorem cell20_651156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_651156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651156 prefixEnd_651156 := by exact prefixLift 651156
  have htrace : WordTrace (prefixWord ++ tailWord_651156) baseStart_651156 baseEnd_651156 := by
    simpa [prefixWord, tailWord_651156, baseEnd_651156] using wordTrace_append hprefix tailTrace_651156
  have hstable : (prefixWord ++ tailWord_651156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651156).length < 2 ^ (prefixWord ++ tailWord_651156).sum := by decide
  have hdescent : baseEnd_651156 < baseStart_651156 := by decide
  rcases family_descends (prefixWord ++ tailWord_651156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651157 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_651157 : Nat := 118140960795 + 651157 * 2 ^ 59
def prefixEnd_651157 : Nat := 4983230072969 + 3 ^ 40 * 651157 * 2
def baseEnd_651157 : Nat := 297205797813168070171457

theorem tailTrace_651157 : CollatzResearch.WordTrace tailWord_651157 prefixEnd_651157 297205797813168070171457 := by
  unfold tailWord_651157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749646901976872606927725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833097934651248404618483 23749646901976872606927725)
  ·
    refine ⟨8906117588241327227597897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23749646901976872606927725 8906117588241327227597897)
    ·
      refine ⟨6679588191180995420698423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8906117588241327227597897 6679588191180995420698423)
      ·
        refine ⟨10019382286771493131047635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6679588191180995420698423 10019382286771493131047635)
        ·
          refine ⟨15029073430157239696571453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10019382286771493131047635 15029073430157239696571453)
          ·
            refine ⟨5635902536308964886214295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15029073430157239696571453 5635902536308964886214295)
            ·
              refine ⟨8453853804463447329321443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635902536308964886214295 8453853804463447329321443)
              ·
                refine ⟨12680780706695170993982165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8453853804463447329321443 12680780706695170993982165)
                ·
                  refine ⟨297205797813168070171457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12680780706695170993982165 297205797813168070171457)
                  ·
                    rfl

theorem cell20_651157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_651157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651157 prefixEnd_651157 := by exact prefixLift 651157
  have htrace : WordTrace (prefixWord ++ tailWord_651157) baseStart_651157 baseEnd_651157 := by
    simpa [prefixWord, tailWord_651157, baseEnd_651157] using wordTrace_append hprefix tailTrace_651157
  have hstable : (prefixWord ++ tailWord_651157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651157).length < 2 ^ (prefixWord ++ tailWord_651157).sum := by decide
  have hdescent : baseEnd_651157 < baseStart_651157 := by decide
  rcases family_descends (prefixWord ++ tailWord_651157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651167 : List Nat := [1, 1, 2, 5, 3, 2, 6]
def baseStart_651167 : Nat := 118140960795 + 651167 * 2 ^ 59
def prefixEnd_651167 : Nat := 4983230072969 + 3 ^ 40 * 651167 * 2
def baseEnd_651167 : Nat := 33023373565072497759787

theorem tailTrace_651167 : CollatzResearch.WordTrace tailWord_651167 prefixEnd_651167 33023373565072497759787 := by
  unfold tailWord_651167
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750011631940644314791755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833341087960429543194503 23750011631940644314791755)
  ·
    refine ⟨35625017447910966472187633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23750011631940644314791755 35625017447910966472187633)
    ·
      refine ⟨26718763085933224854140725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35625017447910966472187633 26718763085933224854140725)
      ·
        refine ⟨2504884039306239830075693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26718763085933224854140725 2504884039306239830075693)
        ·
          refine ⟨939331514739839936278385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2504884039306239830075693 939331514739839936278385)
          ·
            refine ⟨704498636054879952208789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939331514739839936278385 704498636054879952208789)
            ·
              refine ⟨33023373565072497759787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 704498636054879952208789 33023373565072497759787)
              ·
                rfl

theorem cell20_651167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_651167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651167 prefixEnd_651167 := by exact prefixLift 651167
  have htrace : WordTrace (prefixWord ++ tailWord_651167) baseStart_651167 baseEnd_651167 := by
    simpa [prefixWord, tailWord_651167, baseEnd_651167] using wordTrace_append hprefix tailTrace_651167
  have hstable : (prefixWord ++ tailWord_651167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651167).length < 2 ^ (prefixWord ++ tailWord_651167).sum := by decide
  have hdescent : baseEnd_651167 < baseStart_651167 := by decide
  rcases family_descends (prefixWord ++ tailWord_651167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651222 : List Nat := [5, 2, 1, 1, 4, 7]
def baseStart_651222 : Nat := 118140960795 + 651222 * 2 ^ 59
def prefixEnd_651222 : Nat := 4983230072969 + 3 ^ 40 * 651222 * 2
def baseEnd_651222 : Nat := 11008720947567286407575

theorem tailTrace_651222 : CollatzResearch.WordTrace tailWord_651222 prefixEnd_651222 11008720947567286407575 := by
  unfold tailWord_651222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484501102921336794252745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15834678431160925805362613 1484501102921336794252745)
  ·
    refine ⟨1113375827191002595689559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1484501102921336794252745 1113375827191002595689559)
    ·
      refine ⟨1670063740786503893534339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113375827191002595689559 1670063740786503893534339)
      ·
        refine ⟨2505095611179755840301509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670063740786503893534339 2505095611179755840301509)
        ·
          refine ⟨469705427096204220056533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2505095611179755840301509 469705427096204220056533)
          ·
            refine ⟨11008720947567286407575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 469705427096204220056533 11008720947567286407575)
            ·
              rfl

theorem cell20_651222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 7].length) (baseStart_651222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651222 prefixEnd_651222 := by exact prefixLift 651222
  have htrace : WordTrace (prefixWord ++ tailWord_651222) baseStart_651222 baseEnd_651222 := by
    simpa [prefixWord, tailWord_651222, baseEnd_651222] using wordTrace_append hprefix tailTrace_651222
  have hstable : (prefixWord ++ tailWord_651222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651222).length < 2 ^ (prefixWord ++ tailWord_651222).sum := by decide
  have hdescent : baseEnd_651222 < baseStart_651222 := by decide
  rcases family_descends (prefixWord ++ tailWord_651222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651226 : List Nat := [3, 1, 1, 2, 5, 8]
def baseStart_651226 : Nat := 118140960795 + 651226 * 2 ^ 59
def prefixEnd_651226 : Nat := 4983230072969 + 3 ^ 40 * 651226 * 2
def baseEnd_651226 : Nat := 11008788566418907291525

theorem tailTrace_651226 : CollatzResearch.WordTrace tailWord_651226 prefixEnd_651226 11008788566418907291525 := by
  unfold tailWord_651226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938040884681724347797383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15834775692484598260793021 5938040884681724347797383)
  ·
    refine ⟨8907061327022586521696075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5938040884681724347797383 8907061327022586521696075)
    ·
      refine ⟨13360591990533879782544113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8907061327022586521696075 13360591990533879782544113)
      ·
        refine ⟨10020443992900409836908085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13360591990533879782544113 10020443992900409836908085)
        ·
          refine ⟨939416624334413422210133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10020443992900409836908085 939416624334413422210133)
          ·
            refine ⟨11008788566418907291525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 939416624334413422210133 11008788566418907291525)
            ·
              rfl

theorem cell20_651226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 8].length) (baseStart_651226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651226 prefixEnd_651226 := by exact prefixLift 651226
  have htrace : WordTrace (prefixWord ++ tailWord_651226) baseStart_651226 baseEnd_651226 := by
    simpa [prefixWord, tailWord_651226, baseEnd_651226] using wordTrace_append hprefix tailTrace_651226
  have hstable : (prefixWord ++ tailWord_651226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651226).length < 2 ^ (prefixWord ++ tailWord_651226).sum := by decide
  have hdescent : baseEnd_651226 < baseStart_651226 := by decide
  rcases family_descends (prefixWord ++ tailWord_651226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651233 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_651233 : Nat := 118140960795 + 651233 * 2 ^ 59
def prefixEnd_651233 : Nat := 4983230072969 + 3 ^ 40 * 651233 * 2
def baseEnd_651233 : Nat := 297240486284049583637813

theorem tailTrace_651233 : CollatzResearch.WordTrace tailWord_651233 prefixEnd_651233 297240486284049583637813 := by
  unfold tailWord_651233
  simp only [CollatzResearch.WordTrace]
  refine ⟨23752418849701537586694353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15834945899801025057796235 23752418849701537586694353)
  ·
    refine ⟨17814314137276153190020765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23752418849701537586694353 17814314137276153190020765)
    ·
      refine ⟨6680367801478557446257787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17814314137276153190020765 6680367801478557446257787)
      ·
        refine ⟨10020551702217836169386681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680367801478557446257787 10020551702217836169386681)
        ·
          refine ⟨7515413776663377127040011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10020551702217836169386681 7515413776663377127040011)
          ·
            refine ⟨11273120664995065690560017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515413776663377127040011 11273120664995065690560017)
            ·
              refine ⟨8454840498746299267920013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11273120664995065690560017 8454840498746299267920013)
              ·
                refine ⟨3170565187029862225470005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8454840498746299267920013 3170565187029862225470005)
                ·
                  refine ⟨297240486284049583637813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170565187029862225470005 297240486284049583637813)
                  ·
                    rfl

theorem cell20_651233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_651233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651233 prefixEnd_651233 := by exact prefixLift 651233
  have htrace : WordTrace (prefixWord ++ tailWord_651233) baseStart_651233 baseEnd_651233 := by
    simpa [prefixWord, tailWord_651233, baseEnd_651233] using wordTrace_append hprefix tailTrace_651233
  have hstable : (prefixWord ++ tailWord_651233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651233).length < 2 ^ (prefixWord ++ tailWord_651233).sum := by decide
  have hdescent : baseEnd_651233 < baseStart_651233 := by decide
  rcases family_descends (prefixWord ++ tailWord_651233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651236 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_651236 : Nat := 118140960795 + 651236 * 2 ^ 59
def prefixEnd_651236 : Nat := 4983230072969 + 3 ^ 40 * 651236 * 2
def baseEnd_651236 : Nat := 297241855565794906537801

theorem tailTrace_651236 : CollatzResearch.WordTrace tailWord_651236 prefixEnd_651236 297241855565794906537801 := by
  unfold tailWord_651236
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876264134345334549526781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15835018845793779399369041 11876264134345334549526781)
  ·
    refine ⟨4453599050379500456072543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11876264134345334549526781 4453599050379500456072543)
    ·
      refine ⟨6680398575569250684108815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453599050379500456072543 6680398575569250684108815)
      ·
        refine ⟨10020597863353876026163223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680398575569250684108815 10020597863353876026163223)
        ·
          refine ⟨15030896795030814039244835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020597863353876026163223 15030896795030814039244835)
          ·
            refine ⟨22546345192546221058867253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15030896795030814039244835 22546345192546221058867253)
            ·
              refine ⟨2113719861801208224268805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22546345192546221058867253 2113719861801208224268805)
              ·
                refine ⟨396322474087726542050401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2113719861801208224268805 396322474087726542050401)
                ·
                  refine ⟨297241855565794906537801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396322474087726542050401 297241855565794906537801)
                  ·
                    rfl

theorem cell20_651236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_651236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651236 prefixEnd_651236 := by exact prefixLift 651236
  have htrace : WordTrace (prefixWord ++ tailWord_651236) baseStart_651236 baseEnd_651236 := by
    simpa [prefixWord, tailWord_651236, baseEnd_651236] using wordTrace_append hprefix tailTrace_651236
  have hstable : (prefixWord ++ tailWord_651236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651236).length < 2 ^ (prefixWord ++ tailWord_651236).sum := by decide
  have hdescent : baseEnd_651236 < baseStart_651236 := by decide
  rcases family_descends (prefixWord ++ tailWord_651236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651257 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_651257 : Nat := 118140960795 + 651257 * 2 ^ 59
def prefixEnd_651257 : Nat := 4983230072969 + 3 ^ 40 * 651257 * 2
def baseEnd_651257 : Nat := 297251440538012166837715

theorem tailTrace_651257 : CollatzResearch.WordTrace tailWord_651257 prefixEnd_651257 297251440538012166837715 := by
  unfold tailWord_651257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753294201614589685568025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15835529467743059790378683 23753294201614589685568025)
  ·
    refine ⟨17814970651210942264176019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23753294201614589685568025 17814970651210942264176019)
    ·
      refine ⟨26722455976816413396264029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17814970651210942264176019 26722455976816413396264029)
      ·
        refine ⟨10020920991306155023599011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26722455976816413396264029 10020920991306155023599011)
        ·
          refine ⟨15031381486959232535398517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020920991306155023599011 15031381486959232535398517)
          ·
            refine ⟨1409192014402428050193611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15031381486959232535398517 1409192014402428050193611)
            ·
              refine ⟨2113788021603642075290417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409192014402428050193611 2113788021603642075290417)
              ·
                refine ⟨1585341016202731556467813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113788021603642075290417 1585341016202731556467813)
                ·
                  refine ⟨297251440538012166837715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585341016202731556467813 297251440538012166837715)
                  ·
                    rfl

theorem cell20_651257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_651257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651257 prefixEnd_651257 := by exact prefixLift 651257
  have htrace : WordTrace (prefixWord ++ tailWord_651257) baseStart_651257 baseEnd_651257 := by
    simpa [prefixWord, tailWord_651257, baseEnd_651257] using wordTrace_append hprefix tailTrace_651257
  have hstable : (prefixWord ++ tailWord_651257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651257).length < 2 ^ (prefixWord ++ tailWord_651257).sum := by decide
  have hdescent : baseEnd_651257 < baseStart_651257 := by decide
  rcases family_descends (prefixWord ++ tailWord_651257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651277 : List Nat := [1, 7, 1, 2, 1, 1, 7]
def baseStart_651277 : Nat := 118140960795 + 651277 * 2 ^ 59
def prefixEnd_651277 : Nat := 4983230072969 + 3 ^ 40 * 651277 * 2
def baseEnd_651277 : Nat := 33028952120331220685663

theorem tailTrace_651277 : CollatzResearch.WordTrace tailWord_651277 prefixEnd_651277 33028952120331220685663 := by
  unfold tailWord_651277
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754023661542133101296085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15836015774361422067530723 23754023661542133101296085)
  ·
    refine ⟨556734929567393744561627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23754023661542133101296085 556734929567393744561627)
    ·
      refine ⟨835102394351090616842441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556734929567393744561627 835102394351090616842441)
      ·
        refine ⟨626326795763317962631831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835102394351090616842441 626326795763317962631831)
        ·
          refine ⟨939490193644976943947747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626326795763317962631831 939490193644976943947747)
          ·
            refine ⟨1409235290467465415921621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939490193644976943947747 1409235290467465415921621)
            ·
              refine ⟨33028952120331220685663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1409235290467465415921621 33028952120331220685663)
              ·
                rfl

theorem cell20_651277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_651277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651277 prefixEnd_651277 := by exact prefixLift 651277
  have htrace : WordTrace (prefixWord ++ tailWord_651277) baseStart_651277 baseEnd_651277 := by
    simpa [prefixWord, tailWord_651277, baseEnd_651277] using wordTrace_append hprefix tailTrace_651277
  have hstable : (prefixWord ++ tailWord_651277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651277).length < 2 ^ (prefixWord ++ tailWord_651277).sum := by decide
  have hdescent : baseEnd_651277 < baseStart_651277 := by decide
  rcases family_descends (prefixWord ++ tailWord_651277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651284 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_651284 : Nat := 118140960795 + 651284 * 2 ^ 59
def prefixEnd_651284 : Nat := 4983230072969 + 3 ^ 40 * 651284 * 2
def baseEnd_651284 : Nat := 297263764073720072937605

theorem tailTrace_651284 : CollatzResearch.WordTrace tailWord_651284 prefixEnd_651284 297263764073720072937605 := by
  unfold tailWord_651284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877139486258386648400453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15836185981677848864533937 11877139486258386648400453)
  ·
    refine ⟨2226963653673447496575085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11877139486258386648400453 2226963653673447496575085)
    ·
      refine ⟨835111370127542811215657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2226963653673447496575085 835111370127542811215657)
      ·
        refine ⟨626333527595657108411743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835111370127542811215657 626333527595657108411743)
        ·
          refine ⟨939500291393485662617615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626333527595657108411743 939500291393485662617615)
          ·
            refine ⟨1409250437090228493926423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939500291393485662617615 1409250437090228493926423)
            ·
              refine ⟨2113875655635342740889635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409250437090228493926423 2113875655635342740889635)
              ·
                refine ⟨3170813483453014111334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113875655635342740889635 3170813483453014111334453)
                ·
                  refine ⟨297263764073720072937605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170813483453014111334453 297263764073720072937605)
                  ·
                    rfl

theorem cell20_651284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_651284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651284 prefixEnd_651284 := by exact prefixLift 651284
  have htrace : WordTrace (prefixWord ++ tailWord_651284) baseStart_651284 baseEnd_651284 := by
    simpa [prefixWord, tailWord_651284, baseEnd_651284] using wordTrace_append hprefix tailTrace_651284
  have hstable : (prefixWord ++ tailWord_651284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651284).length < 2 ^ (prefixWord ++ tailWord_651284).sum := by decide
  have hdescent : baseEnd_651284 < baseStart_651284 := by decide
  rcases family_descends (prefixWord ++ tailWord_651284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651295 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_651295 : Nat := 118140960795 + 651295 * 2 ^ 59
def prefixEnd_651295 : Nat := 4983230072969 + 3 ^ 40 * 651295 * 2
def baseEnd_651295 : Nat := 297268784773452923570893

theorem tailTrace_651295 : CollatzResearch.WordTrace tailWord_651295 prefixEnd_651295 297268784773452923570893 := by
  unfold tailWord_651295
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754680175476922175451339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15836453450317948116967559 23754680175476922175451339)
  ·
    refine ⟨35632020263215383263177009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23754680175476922175451339 35632020263215383263177009)
    ·
      refine ⟨26724015197411537447382757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35632020263215383263177009 26724015197411537447382757)
      ·
        refine ⟨5010752849514663271384267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26724015197411537447382757 5010752849514663271384267)
        ·
          refine ⟨7516129274271994907076401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010752849514663271384267 7516129274271994907076401)
          ·
            refine ⟨5637096955703996180307301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7516129274271994907076401 5637096955703996180307301)
            ·
              refine ⟨1056955679194499283807619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5637096955703996180307301 1056955679194499283807619)
              ·
                refine ⟨1585433518791748925711429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056955679194499283807619 1585433518791748925711429)
                ·
                  refine ⟨297268784773452923570893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585433518791748925711429 297268784773452923570893)
                  ·
                    rfl

theorem cell20_651295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_651295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651295 prefixEnd_651295 := by exact prefixLift 651295
  have htrace : WordTrace (prefixWord ++ tailWord_651295) baseStart_651295 baseEnd_651295 := by
    simpa [prefixWord, tailWord_651295, baseEnd_651295] using wordTrace_append hprefix tailTrace_651295
  have hstable : (prefixWord ++ tailWord_651295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651295).length < 2 ^ (prefixWord ++ tailWord_651295).sum := by decide
  have hdescent : baseEnd_651295 < baseStart_651295 := by decide
  rcases family_descends (prefixWord ++ tailWord_651295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_651323 : Nat := 118140960795 + 651323 * 2 ^ 59
def prefixEnd_651323 : Nat := 4983230072969 + 3 ^ 40 * 651323 * 2
def baseEnd_651323 : Nat := 99093854912136423545815

theorem tailTrace_651323 : CollatzResearch.WordTrace tailWord_651323 prefixEnd_651323 99093854912136423545815 := by
  unfold tailWord_651323
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755701419375482957470623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15837134279583655304980415 23755701419375482957470623)
  ·
    refine ⟨35633552129063224436205935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23755701419375482957470623 35633552129063224436205935)
    ·
      refine ⟨53450328193594836654308903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35633552129063224436205935 53450328193594836654308903)
      ·
        refine ⟨80175492290392254981463355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53450328193594836654308903 80175492290392254981463355)
        ·
          refine ⟨120263238435588382472195033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80175492290392254981463355 120263238435588382472195033)
          ·
            refine ⟨90197428826691286854146275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120263238435588382472195033 90197428826691286854146275)
            ·
              refine ⟨135296143240036930281219413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90197428826691286854146275 135296143240036930281219413)
              ·
                refine ⟨99093854912136423545815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 135296143240036930281219413 99093854912136423545815)
                ·
                  rfl

theorem cell20_651323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_651323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651323 prefixEnd_651323 := by exact prefixLift 651323
  have htrace : WordTrace (prefixWord ++ tailWord_651323) baseStart_651323 baseEnd_651323 := by
    simpa [prefixWord, tailWord_651323, baseEnd_651323] using wordTrace_append hprefix tailTrace_651323
  have hstable : (prefixWord ++ tailWord_651323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651323).length < 2 ^ (prefixWord ++ tailWord_651323).sum := by decide
  have hdescent : baseEnd_651323 < baseStart_651323 := by decide
  rcases family_descends (prefixWord ++ tailWord_651323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651329 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 2]
def baseStart_651329 : Nat := 118140960795 + 651329 * 2 ^ 59
def prefixEnd_651329 : Nat := 4983230072969 + 3 ^ 40 * 651329 * 2
def baseEnd_651329 : Nat := 297284303299899916437421

theorem tailTrace_651329 : CollatzResearch.WordTrace tailWord_651329 prefixEnd_651329 297284303299899916437421 := by
  unfold tailWord_651329
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755920257353745982189041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15837280171569163988126027 23755920257353745982189041)
  ·
    refine ⟨17816940193015309486641781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23755920257353745982189041 17816940193015309486641781)
    ·
      refine ⟨1670338143095185264372667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17816940193015309486641781 1670338143095185264372667)
      ·
        refine ⟨2505507214642777896559001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670338143095185264372667 2505507214642777896559001)
        ·
          refine ⟨1879130410982083422419251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2505507214642777896559001 1879130410982083422419251)
          ·
            refine ⟨2818695616473125133628877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879130410982083422419251 2818695616473125133628877)
            ·
              refine ⟨1057010856177421925110829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818695616473125133628877 1057010856177421925110829)
              ·
                refine ⟨396379071066533221916561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057010856177421925110829 396379071066533221916561)
                ·
                  refine ⟨297284303299899916437421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396379071066533221916561 297284303299899916437421)
                  ·
                    rfl

theorem cell20_651329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_651329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651329 prefixEnd_651329 := by exact prefixLift 651329
  have htrace : WordTrace (prefixWord ++ tailWord_651329) baseStart_651329 baseEnd_651329 := by
    simpa [prefixWord, tailWord_651329, baseEnd_651329] using wordTrace_append hprefix tailTrace_651329
  have hstable : (prefixWord ++ tailWord_651329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651329).length < 2 ^ (prefixWord ++ tailWord_651329).sum := by decide
  have hdescent : baseEnd_651329 < baseStart_651329 := by decide
  rcases family_descends (prefixWord ++ tailWord_651329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651346 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_651346 : Nat := 118140960795 + 651346 * 2 ^ 59
def prefixEnd_651346 : Nat := 4983230072969 + 3 ^ 40 * 651346 * 2
def baseEnd_651346 : Nat := 297292062563123412870685

theorem tailTrace_651346 : CollatzResearch.WordTrace tailWord_651346 prefixEnd_651346 297292062563123412870685 := by
  unfold tailWord_651346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939135074573039471389473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15837693532194771923705261 5939135074573039471389473)
  ·
    refine ⟨4454351305929779603542105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5939135074573039471389473 4454351305929779603542105)
    ·
      refine ⟨3340763479447334702656579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4454351305929779603542105 3340763479447334702656579)
      ·
        refine ⟨5011145219171002053984869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340763479447334702656579 5011145219171002053984869)
        ·
          refine ⟨939589728594562885122163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5011145219171002053984869 939589728594562885122163)
          ·
            refine ⟨1409384592891844327683245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939589728594562885122163 1409384592891844327683245)
            ·
              refine ⟨528519222334441622881217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409384592891844327683245 528519222334441622881217)
              ·
                refine ⟨396389416750831217160913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528519222334441622881217 396389416750831217160913)
                ·
                  refine ⟨297292062563123412870685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396389416750831217160913 297292062563123412870685)
                  ·
                    rfl

theorem cell20_651346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_651346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651346 prefixEnd_651346 := by exact prefixLift 651346
  have htrace : WordTrace (prefixWord ++ tailWord_651346) baseStart_651346 baseEnd_651346 := by
    simpa [prefixWord, tailWord_651346, baseEnd_651346] using wordTrace_append hprefix tailTrace_651346
  have hstable : (prefixWord ++ tailWord_651346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651346).length < 2 ^ (prefixWord ++ tailWord_651346).sum := by decide
  have hdescent : baseEnd_651346 < baseStart_651346 := by decide
  rcases family_descends (prefixWord ++ tailWord_651346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651357 : List Nat := [1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_651357 : Nat := 118140960795 + 651357 * 2 ^ 59
def prefixEnd_651357 : Nat := 4983230072969 + 3 ^ 40 * 651357 * 2
def baseEnd_651357 : Nat := 99099027754285421167991

theorem tailTrace_651357 : CollatzResearch.WordTrace tailWord_651357 prefixEnd_651357 99099027754285421167991 := by
  unfold tailWord_651357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23756941501252306764208325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15837961000834871176138883 23756941501252306764208325)
  ·
    refine ⟨4454426531484807518289061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23756941501252306764208325 4454426531484807518289061)
    ·
      refine ⟨835204974653401409679199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4454426531484807518289061 835204974653401409679199)
      ·
        refine ⟨1252807461980102114518799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835204974653401409679199 1252807461980102114518799)
        ·
          refine ⟨1879211192970153171778199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252807461980102114518799 1879211192970153171778199)
          ·
            refine ⟨2818816789455229757667299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879211192970153171778199 2818816789455229757667299)
            ·
              refine ⟨4228225184182844636500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818816789455229757667299 4228225184182844636500949)
              ·
                refine ⟨99099027754285421167991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4228225184182844636500949 99099027754285421167991)
                ·
                  rfl

theorem cell20_651357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_651357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651357 prefixEnd_651357 := by exact prefixLift 651357
  have htrace : WordTrace (prefixWord ++ tailWord_651357) baseStart_651357 baseEnd_651357 := by
    simpa [prefixWord, tailWord_651357, baseEnd_651357] using wordTrace_append hprefix tailTrace_651357
  have hstable : (prefixWord ++ tailWord_651357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651357).length < 2 ^ (prefixWord ++ tailWord_651357).sum := by decide
  have hdescent : baseEnd_651357 < baseStart_651357 := by decide
  rcases family_descends (prefixWord ++ tailWord_651357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651378 : List Nat := [3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_651378 : Nat := 118140960795 + 651378 * 2 ^ 59
def prefixEnd_651378 : Nat := 4983230072969 + 3 ^ 40 * 651378 * 2
def baseEnd_651378 : Nat := 99102222745024507934629

theorem tailTrace_651378 : CollatzResearch.WordTrace tailWord_651378 prefixEnd_651378 99102222745024507934629 := by
  unfold tailWord_651378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939426858544056837680697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15838471622784151567148525 5939426858544056837680697)
  ·
    refine ⟨4454570143908042628260523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5939426858544056837680697 4454570143908042628260523)
    ·
      refine ⟨6681855215862063942390785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4454570143908042628260523 6681855215862063942390785)
      ·
        refine ⟨5011391411896547956793089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6681855215862063942390785 5011391411896547956793089)
        ·
          refine ⟨3758543558922410967594817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011391411896547956793089 3758543558922410967594817)
          ·
            refine ⟨2818907669191808225696113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758543558922410967594817 2818907669191808225696113)
            ·
              refine ⟨2114180751893856169272085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818907669191808225696113 2114180751893856169272085)
              ·
                refine ⟨99102222745024507934629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2114180751893856169272085 99102222745024507934629)
                ·
                  rfl

theorem cell20_651378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_651378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651378 prefixEnd_651378 := by exact prefixLift 651378
  have htrace : WordTrace (prefixWord ++ tailWord_651378) baseStart_651378 baseEnd_651378 := by
    simpa [prefixWord, tailWord_651378, baseEnd_651378] using wordTrace_append hprefix tailTrace_651378
  have hstable : (prefixWord ++ tailWord_651378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651378).length < 2 ^ (prefixWord ++ tailWord_651378).sum := by decide
  have hdescent : baseEnd_651378 < baseStart_651378 := by decide
  rcases family_descends (prefixWord ++ tailWord_651378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651402 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_651402 : Nat := 118140960795 + 651402 * 2 ^ 59
def prefixEnd_651402 : Nat := 4983230072969 + 3 ^ 40 * 651402 * 2
def baseEnd_651402 : Nat := 297317622489036107003789

theorem tailTrace_651402 : CollatzResearch.WordTrace tailWord_651402 prefixEnd_651402 297317622489036107003789 := by
  unfold tailWord_651402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939645696522319862399115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15839055190726186299730973 5939645696522319862399115)
  ·
    refine ⟨8909468544783479793598673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5939645696522319862399115 8909468544783479793598673)
    ·
      refine ⟨6682101408587609845199005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8909468544783479793598673 6682101408587609845199005)
      ·
        refine ⟨2505788028220353691949627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6682101408587609845199005 2505788028220353691949627)
        ·
          refine ⟨3758682042330530537924441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505788028220353691949627 3758682042330530537924441)
          ·
            refine ⟨2819011531747897903443331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758682042330530537924441 2819011531747897903443331)
            ·
              refine ⟨4228517297621846855164997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819011531747897903443331 4228517297621846855164997)
              ·
                refine ⟨792846993304096285343437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4228517297621846855164997 792846993304096285343437)
                ·
                  refine ⟨297317622489036107003789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792846993304096285343437 297317622489036107003789)
                  ·
                    rfl

theorem cell20_651402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_651402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651402 prefixEnd_651402 := by exact prefixLift 651402
  have htrace : WordTrace (prefixWord ++ tailWord_651402) baseStart_651402 baseEnd_651402 := by
    simpa [prefixWord, tailWord_651402, baseEnd_651402] using wordTrace_append hprefix tailTrace_651402
  have hstable : (prefixWord ++ tailWord_651402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651402).length < 2 ^ (prefixWord ++ tailWord_651402).sum := by decide
  have hdescent : baseEnd_651402 < baseStart_651402 := by decide
  rcases family_descends (prefixWord ++ tailWord_651402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651426 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_651426 : Nat := 118140960795 + 651426 * 2 ^ 59
def prefixEnd_651426 : Nat := 4983230072969 + 3 ^ 40 * 651426 * 2
def baseEnd_651426 : Nat := 297328576742998690203691

theorem tailTrace_651426 : CollatzResearch.WordTrace tailWord_651426 prefixEnd_651426 297328576742998690203691 := by
  unfold tailWord_651426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939864534500582887117533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15839638758668221032313421 5939864534500582887117533)
  ·
    refine ⟨2227449200437718582669075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5939864534500582887117533 2227449200437718582669075)
    ·
      refine ⟨3341173800656577874003613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227449200437718582669075 3341173800656577874003613)
      ·
        refine ⟨1252940175246216702751355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3341173800656577874003613 1252940175246216702751355)
        ·
          refine ⟨1879410262869325054127033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252940175246216702751355 1879410262869325054127033)
          ·
            refine ⟨1409557697151993790595275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1879410262869325054127033 1409557697151993790595275)
            ·
              refine ⟨2114336545727990685892913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409557697151993790595275 2114336545727990685892913)
              ·
                refine ⟨1585752409295993014419685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114336545727990685892913 1585752409295993014419685)
                ·
                  refine ⟨297328576742998690203691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585752409295993014419685 297328576742998690203691)
                  ·
                    rfl

theorem cell20_651426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_651426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651426 prefixEnd_651426 := by exact prefixLift 651426
  have htrace : WordTrace (prefixWord ++ tailWord_651426) baseStart_651426 baseEnd_651426 := by
    simpa [prefixWord, tailWord_651426, baseEnd_651426] using wordTrace_append hprefix tailTrace_651426
  have hstable : (prefixWord ++ tailWord_651426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651426).length < 2 ^ (prefixWord ++ tailWord_651426).sum := by decide
  have hdescent : baseEnd_651426 < baseStart_651426 := by decide
  rcases family_descends (prefixWord ++ tailWord_651426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651457 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_651457 : Nat := 118140960795 + 651457 * 2 ^ 59
def prefixEnd_651457 : Nat := 4983230072969 + 3 ^ 40 * 651457 * 2
def baseEnd_651457 : Nat := 297342725987700360170231

theorem tailTrace_651457 : CollatzResearch.WordTrace tailWord_651457 prefixEnd_651457 297342725987700360170231 := by
  unfold tailWord_651457
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760588800890023842848625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15840392533926682561899083 23760588800890023842848625)
  ·
    refine ⟨17820441600667517882136469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23760588800890023842848625 17820441600667517882136469)
    ·
      refine ⟨835333200031289900725147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17820441600667517882136469 835333200031289900725147)
      ·
        refine ⟨1252999800046934851087721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835333200031289900725147 1252999800046934851087721)
        ·
          refine ⟨939749850035201138315791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252999800046934851087721 939749850035201138315791)
          ·
            refine ⟨1409624775052801707473687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939749850035201138315791 1409624775052801707473687)
            ·
              refine ⟨2114437162579202561210531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409624775052801707473687 2114437162579202561210531)
              ·
                refine ⟨3171655743868803841815797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114437162579202561210531 3171655743868803841815797)
                ·
                  refine ⟨297342725987700360170231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3171655743868803841815797 297342725987700360170231)
                  ·
                    rfl

theorem cell20_651457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_651457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651457 prefixEnd_651457 := by exact prefixLift 651457
  have htrace : WordTrace (prefixWord ++ tailWord_651457) baseStart_651457 baseEnd_651457 := by
    simpa [prefixWord, tailWord_651457, baseEnd_651457] using wordTrace_append hprefix tailTrace_651457
  have hstable : (prefixWord ++ tailWord_651457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651457).length < 2 ^ (prefixWord ++ tailWord_651457).sum := by decide
  have hdescent : baseEnd_651457 < baseStart_651457 := by decide
  rcases family_descends (prefixWord ++ tailWord_651457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651484 : List Nat := [2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_651484 : Nat := 118140960795 + 651484 * 2 ^ 59
def prefixEnd_651484 : Nat := 4983230072969 + 3 ^ 40 * 651484 * 2
def baseEnd_651484 : Nat := 99118349841136088756707

theorem tailTrace_651484 : CollatzResearch.WordTrace tailWord_651484 prefixEnd_651484 99118349841136088756707 := by
  unfold tailWord_651484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880786785896103727040753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15841049047861471636054337 11880786785896103727040753)
  ·
    refine ⟨8910590089422077795280565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11880786785896103727040753 8910590089422077795280565)
    ·
      refine ⟨835367820883319793307553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8910590089422077795280565 835367820883319793307553)
      ·
        refine ⟨626525865662489844980665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835367820883319793307553 626525865662489844980665)
        ·
          refine ⟨469894399246867383735499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626525865662489844980665 469894399246867383735499)
          ·
            refine ⟨704841598870301075603249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469894399246867383735499 704841598870301075603249)
            ·
              refine ⟨528631199152725806702437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704841598870301075603249 528631199152725806702437)
              ·
                refine ⟨99118349841136088756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528631199152725806702437 99118349841136088756707)
                ·
                  rfl

theorem cell20_651484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_651484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651484 prefixEnd_651484 := by exact prefixLift 651484
  have htrace : WordTrace (prefixWord ++ tailWord_651484) baseStart_651484 baseEnd_651484 := by
    simpa [prefixWord, tailWord_651484, baseEnd_651484] using wordTrace_append hprefix tailTrace_651484
  have hstable : (prefixWord ++ tailWord_651484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651484).length < 2 ^ (prefixWord ++ tailWord_651484).sum := by decide
  have hdescent : baseEnd_651484 < baseStart_651484 := by decide
  rcases family_descends (prefixWord ++ tailWord_651484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651544 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_651544 : Nat := 118140960795 + 651544 * 2 ^ 59
def prefixEnd_651544 : Nat := 4983230072969 + 3 ^ 40 * 651544 * 2
def baseEnd_651544 : Nat := 297382435158314724269875

theorem tailTrace_651544 : CollatzResearch.WordTrace tailWord_651544 prefixEnd_651544 297382435158314724269875 := by
  unfold tailWord_651544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881880975787418850632843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15842507967716558467510457 11881880975787418850632843)
  ·
    refine ⟨17822821463681128275949265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11881880975787418850632843 17822821463681128275949265)
    ·
      refine ⟨13367116097760846206961949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17822821463681128275949265 13367116097760846206961949)
      ·
        refine ⟨5012668536660317327610731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13367116097760846206961949 5012668536660317327610731)
        ·
          refine ⟨7519002804990475991416097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012668536660317327610731 7519002804990475991416097)
          ·
            refine ⟨5639252103742856993562073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7519002804990475991416097 5639252103742856993562073)
            ·
              refine ⟨4229439077807142745171555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5639252103742856993562073 4229439077807142745171555)
              ·
                refine ⟨6344158616710714117757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229439077807142745171555 6344158616710714117757333)
                ·
                  refine ⟨297382435158314724269875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6344158616710714117757333 297382435158314724269875)
                  ·
                    rfl

theorem cell20_651544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_651544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651544 prefixEnd_651544 := by exact prefixLift 651544
  have htrace : WordTrace (prefixWord ++ tailWord_651544) baseStart_651544 baseEnd_651544 := by
    simpa [prefixWord, tailWord_651544, baseEnd_651544] using wordTrace_append hprefix tailTrace_651544
  have hstable : (prefixWord ++ tailWord_651544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651544).length < 2 ^ (prefixWord ++ tailWord_651544).sum := by decide
  have hdescent : baseEnd_651544 < baseStart_651544 := by decide
  rcases family_descends (prefixWord ++ tailWord_651544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651578 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_651578 : Nat := 118140960795 + 651578 * 2 ^ 59
def prefixEnd_651578 : Nat := 4983230072969 + 3 ^ 40 * 651578 * 2
def baseEnd_651578 : Nat := 297397953684761717136403

theorem tailTrace_651578 : CollatzResearch.WordTrace tailWord_651578 prefixEnd_651578 297397953684761717136403 := by
  unfold tailWord_651578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941250508362915377000847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15843334688967774338668925 5941250508362915377000847)
  ·
    refine ⟨8911875762544373065501271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5941250508362915377000847 8911875762544373065501271)
    ·
      refine ⟨13367813643816559598251907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8911875762544373065501271 13367813643816559598251907)
      ·
        refine ⟨20051720465724839397377861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13367813643816559598251907 20051720465724839397377861)
        ·
          refine ⟨3759697587323407387008349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20051720465724839397377861 3759697587323407387008349)
          ·
            refine ⟨1409886595246277770128131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3759697587323407387008349 1409886595246277770128131)
            ·
              refine ⟨2114829892869416655192197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409886595246277770128131 2114829892869416655192197)
              ·
                refine ⟨396530604913015622848537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2114829892869416655192197 396530604913015622848537)
                ·
                  refine ⟨297397953684761717136403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396530604913015622848537 297397953684761717136403)
                  ·
                    rfl

theorem cell20_651578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_651578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651578 prefixEnd_651578 := by exact prefixLift 651578
  have htrace : WordTrace (prefixWord ++ tailWord_651578) baseStart_651578 baseEnd_651578 := by
    simpa [prefixWord, tailWord_651578, baseEnd_651578] using wordTrace_append hprefix tailTrace_651578
  have hstable : (prefixWord ++ tailWord_651578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651578).length < 2 ^ (prefixWord ++ tailWord_651578).sum := by decide
  have hdescent : baseEnd_651578 < baseStart_651578 := by decide
  rcases family_descends (prefixWord ++ tailWord_651578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651612 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_651612 : Nat := 118140960795 + 651612 * 2 ^ 59
def prefixEnd_651612 : Nat := 4983230072969 + 3 ^ 40 * 651612 * 2
def baseEnd_651612 : Nat := 297413472211208710002931

theorem tailTrace_651612 : CollatzResearch.WordTrace tailWord_651612 prefixEnd_651612 297413472211208710002931 := by
  unfold tailWord_651612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883121057664242657370545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15844161410218990209827393 11883121057664242657370545)
  ·
    refine ⟨8912340793248181993027909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11883121057664242657370545 8912340793248181993027909)
    ·
      refine ⟨1671063898734034123692733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8912340793248181993027909 1671063898734034123692733)
      ·
        refine ⟨626648962025262796384775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1671063898734034123692733 626648962025262796384775)
        ·
          refine ⟨939973443037894194577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626648962025262796384775 939973443037894194577163)
          ·
            refine ⟨1409960164556841291865745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939973443037894194577163 1409960164556841291865745)
            ·
              refine ⟨1057470123417630968899309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409960164556841291865745 1057470123417630968899309)
              ·
                refine ⟨396551296281611613337241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057470123417630968899309 396551296281611613337241)
                ·
                  refine ⟨297413472211208710002931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396551296281611613337241 297413472211208710002931)
                  ·
                    rfl

theorem cell20_651612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_651612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651612 prefixEnd_651612 := by exact prefixLift 651612
  have htrace : WordTrace (prefixWord ++ tailWord_651612) baseStart_651612 baseEnd_651612 := by
    simpa [prefixWord, tailWord_651612, baseEnd_651612] using wordTrace_append hprefix tailTrace_651612
  have hstable : (prefixWord ++ tailWord_651612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651612).length < 2 ^ (prefixWord ++ tailWord_651612).sum := by decide
  have hdescent : baseEnd_651612 < baseStart_651612 := by decide
  rcases family_descends (prefixWord ++ tailWord_651612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651620 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_651620 : Nat := 118140960795 + 651620 * 2 ^ 59
def prefixEnd_651620 : Nat := 4983230072969 + 3 ^ 40 * 651620 * 2
def baseEnd_651620 : Nat := 297417123629196237736231

theorem tailTrace_651620 : CollatzResearch.WordTrace tailWord_651620 prefixEnd_651620 297417123629196237736231 := by
  unfold tailWord_651620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883266949649751340516157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15844355932866335120688209 11883266949649751340516157)
  ·
    refine ⟨4456225106118656752693559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11883266949649751340516157 4456225106118656752693559)
    ·
      refine ⟨6684337659177985129040339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456225106118656752693559 6684337659177985129040339)
      ·
        refine ⟨10026506488766977693560509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6684337659177985129040339 10026506488766977693560509)
        ·
          refine ⟨3759939933287616635085191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10026506488766977693560509 3759939933287616635085191)
          ·
            refine ⟨5639909899931424952627787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759939933287616635085191 5639909899931424952627787)
            ·
              refine ⟨8459864849897137428941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639909899931424952627787 8459864849897137428941681)
              ·
                refine ⟨6344898637422853071706261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8459864849897137428941681 6344898637422853071706261)
                ·
                  refine ⟨297417123629196237736231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6344898637422853071706261 297417123629196237736231)
                  ·
                    rfl

theorem cell20_651620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_651620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651620 prefixEnd_651620 := by exact prefixLift 651620
  have htrace : WordTrace (prefixWord ++ tailWord_651620) baseStart_651620 baseEnd_651620 := by
    simpa [prefixWord, tailWord_651620, baseEnd_651620] using wordTrace_append hprefix tailTrace_651620
  have hstable : (prefixWord ++ tailWord_651620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651620).length < 2 ^ (prefixWord ++ tailWord_651620).sum := by decide
  have hdescent : baseEnd_651620 < baseStart_651620 := by decide
  rcases family_descends (prefixWord ++ tailWord_651620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651637 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_651637 : Nat := 118140960795 + 651637 * 2 ^ 59
def prefixEnd_651637 : Nat := 4983230072969 + 3 ^ 40 * 651637 * 2
def baseEnd_651637 : Nat := 297424882892419734169495

theorem tailTrace_651637 : CollatzResearch.WordTrace tailWord_651637 prefixEnd_651637 297424882892419734169495 := by
  unfold tailWord_651637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767153940237914584401165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15844769293491943056267443 23767153940237914584401165)
  ·
    refine ⟨8912682727589217969150437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23767153940237914584401165 8912682727589217969150437)
    ·
      refine ⟨1671128011422978369215707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8912682727589217969150437 1671128011422978369215707)
      ·
        refine ⟨2506692017134467553823561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671128011422978369215707 2506692017134467553823561)
        ·
          refine ⟨1880019012850850665367671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506692017134467553823561 1880019012850850665367671)
          ·
            refine ⟨2820028519276275998051507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880019012850850665367671 2820028519276275998051507)
            ·
              refine ⟨4230042778914413997077261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820028519276275998051507 4230042778914413997077261)
              ·
                refine ⟨1586266042092905248903973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4230042778914413997077261 1586266042092905248903973)
                ·
                  refine ⟨297424882892419734169495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586266042092905248903973 297424882892419734169495)
                  ·
                    rfl

theorem cell20_651637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_651637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651637 prefixEnd_651637 := by exact prefixLift 651637
  have htrace : WordTrace (prefixWord ++ tailWord_651637) baseStart_651637 baseEnd_651637 := by
    simpa [prefixWord, tailWord_651637, baseEnd_651637] using wordTrace_append hprefix tailTrace_651637
  have hstable : (prefixWord ++ tailWord_651637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651637).length < 2 ^ (prefixWord ++ tailWord_651637).sum := by decide
  have hdescent : baseEnd_651637 < baseStart_651637 := by decide
  rcases family_descends (prefixWord ++ tailWord_651637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651688 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_651688 : Nat := 118140960795 + 651688 * 2 ^ 59
def prefixEnd_651688 : Nat := 4983230072969 + 3 ^ 40 * 651688 * 2
def baseEnd_651688 : Nat := 297448160682090223469287

theorem tailTrace_651688 : CollatzResearch.WordTrace tailWord_651688 prefixEnd_651688 297448160682090223469287 := by
  unfold tailWord_651688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11884507031526575147253859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15846009375368766863005145 11884507031526575147253859)
  ·
    refine ⟨17826760547289862720880789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11884507031526575147253859 17826760547289862720880789)
    ·
      refine ⟨835629400654212315041287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17826760547289862720880789 835629400654212315041287)
      ·
        refine ⟨1253444100981318472561931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835629400654212315041287 1253444100981318472561931)
        ·
          refine ⟨1880166151471977708842897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253444100981318472561931 1880166151471977708842897)
          ·
            refine ⟨1410124613603983281632173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880166151471977708842897 1410124613603983281632173)
            ·
              refine ⟨528796730101493730612065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1410124613603983281632173 528796730101493730612065)
              ·
                refine ⟨396597547576120297959049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528796730101493730612065 396597547576120297959049)
                ·
                  refine ⟨297448160682090223469287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396597547576120297959049 297448160682090223469287)
                  ·
                    rfl

theorem cell20_651688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_651688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651688 prefixEnd_651688 := by exact prefixLift 651688
  have htrace : WordTrace (prefixWord ++ tailWord_651688) baseStart_651688 baseEnd_651688 := by
    simpa [prefixWord, tailWord_651688, baseEnd_651688] using wordTrace_append hprefix tailTrace_651688
  have hstable : (prefixWord ++ tailWord_651688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651688).length < 2 ^ (prefixWord ++ tailWord_651688).sum := by decide
  have hdescent : baseEnd_651688 < baseStart_651688 := by decide
  rcases family_descends (prefixWord ++ tailWord_651688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651703 : List Nat := [1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_651703 : Nat := 118140960795 + 651703 * 2 ^ 59
def prefixEnd_651703 : Nat := 4983230072969 + 3 ^ 40 * 651703 * 2
def baseEnd_651703 : Nat := 99151669030272279323075

theorem tailTrace_651703 : CollatzResearch.WordTrace tailWord_651703 prefixEnd_651703 99151669030272279323075 := by
  unfold tailWord_651703
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769561157998807856303763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15846374105332538570869175 23769561157998807856303763)
  ·
    refine ⟨35654341736998211784455645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23769561157998807856303763 35654341736998211784455645)
    ·
      refine ⟨13370378151374329419170867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35654341736998211784455645 13370378151374329419170867)
      ·
        refine ⟨20055567227061494128756301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13370378151374329419170867 20055567227061494128756301)
        ·
          refine ⟨7520837710148060298283613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20055567227061494128756301 7520837710148060298283613)
          ·
            refine ⟨2820314141305522611856355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7520837710148060298283613 2820314141305522611856355)
            ·
              refine ⟨4230471211958283917784533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820314141305522611856355 4230471211958283917784533)
              ·
                refine ⟨99151669030272279323075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4230471211958283917784533 99151669030272279323075)
                ·
                  rfl

theorem cell20_651703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_651703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651703 prefixEnd_651703 := by exact prefixLift 651703
  have htrace : WordTrace (prefixWord ++ tailWord_651703) baseStart_651703 baseEnd_651703 := by
    simpa [prefixWord, tailWord_651703, baseEnd_651703] using wordTrace_append hprefix tailTrace_651703
  have hstable : (prefixWord ++ tailWord_651703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651703).length < 2 ^ (prefixWord ++ tailWord_651703).sum := by decide
  have hdescent : baseEnd_651703 < baseStart_651703 := by decide
  rcases family_descends (prefixWord ++ tailWord_651703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651758 : List Nat := [4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_651758 : Nat := 118140960795 + 651758 * 2 ^ 59
def prefixEnd_651758 : Nat := 4983230072969 + 3 ^ 40 * 651758 * 2
def baseEnd_651758 : Nat := 99160036863160363711889

theorem tailTrace_651758 : CollatzResearch.WordTrace tailWord_651758 prefixEnd_651758 99160036863160363711889 := by
  unfold tailWord_651758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971445896599944031194491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15847711448533034833037285 2971445896599944031194491)
  ·
    refine ⟨4457168844899916046791737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971445896599944031194491 4457168844899916046791737)
    ·
      refine ⟨3342876633674937035093803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4457168844899916046791737 3342876633674937035093803)
      ·
        refine ⟨5014314950512405552640705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342876633674937035093803 5014314950512405552640705)
        ·
          refine ⟨3760736212884304164480529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5014314950512405552640705 3760736212884304164480529)
          ·
            refine ⟨2820552159663228123360397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3760736212884304164480529 2820552159663228123360397)
            ·
              refine ⟨1057707059873710546260149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2820552159663228123360397 1057707059873710546260149)
              ·
                refine ⟨99160036863160363711889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1057707059873710546260149 99160036863160363711889)
                ·
                  rfl

theorem cell20_651758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_651758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651758 prefixEnd_651758 := by exact prefixLift 651758
  have htrace : WordTrace (prefixWord ++ tailWord_651758) baseStart_651758 baseEnd_651758 := by
    simpa [prefixWord, tailWord_651758, baseEnd_651758] using wordTrace_append hprefix tailTrace_651758
  have hstable : (prefixWord ++ tailWord_651758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651758).length < 2 ^ (prefixWord ++ tailWord_651758).sum := by decide
  have hdescent : baseEnd_651758 < baseStart_651758 := by decide
  rcases family_descends (prefixWord ++ tailWord_651758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651830 : List Nat := [5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_651830 : Nat := 118140960795 + 651830 * 2 ^ 59
def prefixEnd_651830 : Nat := 4983230072969 + 3 ^ 40 * 651830 * 2
def baseEnd_651830 : Nat := 99170991117122946911791

theorem tailTrace_651830 : CollatzResearch.WordTrace tailWord_651830 prefixEnd_651830 99170991117122946911791 := by
  unfold tailWord_651830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485887076783669284136059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15849462152359139030784629 1485887076783669284136059)
  ·
    refine ⟨2228830615175503926204089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1485887076783669284136059 2228830615175503926204089)
    ·
      refine ⟨1671622961381627944653067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2228830615175503926204089 1671622961381627944653067)
      ·
        refine ⟨2507434442072441916979601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671622961381627944653067 2507434442072441916979601)
        ·
          refine ⟨1880575831554331437734701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507434442072441916979601 1880575831554331437734701)
          ·
            refine ⟨705215936832874289150513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1880575831554331437734701 705215936832874289150513)
            ·
              refine ⟨528911952624655716862885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705215936832874289150513 528911952624655716862885)
              ·
                refine ⟨99170991117122946911791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528911952624655716862885 99170991117122946911791)
                ·
                  rfl

theorem cell20_651830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_651830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651830 prefixEnd_651830 := by exact prefixLift 651830
  have htrace : WordTrace (prefixWord ++ tailWord_651830) baseStart_651830 baseEnd_651830 := by
    simpa [prefixWord, tailWord_651830, baseEnd_651830] using wordTrace_append hprefix tailTrace_651830
  have hstable : (prefixWord ++ tailWord_651830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651830).length < 2 ^ (prefixWord ++ tailWord_651830).sum := by decide
  have hdescent : baseEnd_651830 < baseStart_651830 := by decide
  rcases family_descends (prefixWord ++ tailWord_651830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651834 : List Nat := [3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_651834 : Nat := 118140960795 + 651834 * 2 ^ 59
def prefixEnd_651834 : Nat := 4983230072969 + 3 ^ 40 * 651834 * 2
def baseEnd_651834 : Nat := 99171599686787534867341

theorem tailTrace_651834 : CollatzResearch.WordTrace tailWord_651834 prefixEnd_651834 99171599686787534867341 := by
  unfold tailWord_651834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943584780131054307330639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15849559413682811486215037 5943584780131054307330639)
  ·
    refine ⟨8915377170196581460995959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943584780131054307330639 8915377170196581460995959)
    ·
      refine ⟨13373065755294872191493939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915377170196581460995959 13373065755294872191493939)
      ·
        refine ⟨20059598632942308287240909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13373065755294872191493939 20059598632942308287240909)
        ·
          refine ⟨7522349487353365607715341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20059598632942308287240909 7522349487353365607715341)
          ·
            refine ⟨2820881057757512102893253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7522349487353365607715341 2820881057757512102893253)
            ·
              refine ⟨528915198329533519292485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2820881057757512102893253 528915198329533519292485)
              ·
                refine ⟨99171599686787534867341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528915198329533519292485 99171599686787534867341)
                ·
                  rfl

theorem cell20_651834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_651834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651834 prefixEnd_651834 := by exact prefixLift 651834
  have htrace : WordTrace (prefixWord ++ tailWord_651834) baseStart_651834 baseEnd_651834 := by
    simpa [prefixWord, tailWord_651834, baseEnd_651834] using wordTrace_append hprefix tailTrace_651834
  have hstable : (prefixWord ++ tailWord_651834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651834).length < 2 ^ (prefixWord ++ tailWord_651834).sum := by decide
  have hdescent : baseEnd_651834 < baseStart_651834 := by decide
  rcases family_descends (prefixWord ++ tailWord_651834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651841 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_651841 : Nat := 118140960795 + 651841 * 2 ^ 59
def prefixEnd_651841 : Nat := 4983230072969 + 3 ^ 40 * 651841 * 2
def baseEnd_651841 : Nat := 297517994051101691368661

theorem tailTrace_651841 : CollatzResearch.WordTrace tailWord_651841 prefixEnd_651841 297517994051101691368661 := by
  unfold tailWord_651841
  simp only [CollatzResearch.WordTrace]
  refine ⟨23774594431498857424827377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15849729620999238283218251 23774594431498857424827377)
  ·
    refine ⟨17830945823624143068620533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23774594431498857424827377 17830945823624143068620533)
    ·
      refine ⟨1671651170964763412683175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17830945823624143068620533 1671651170964763412683175)
      ·
        refine ⟨2507476756447145119024763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671651170964763412683175 2507476756447145119024763)
        ·
          refine ⟨3761215134670717678537145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507476756447145119024763 3761215134670717678537145)
          ·
            refine ⟨2820911351003038258902859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3761215134670717678537145 2820911351003038258902859)
            ·
              refine ⟨4231367026504557388354289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820911351003038258902859 4231367026504557388354289)
              ·
                refine ⟨3173525269878418041265717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4231367026504557388354289 3173525269878418041265717)
                ·
                  refine ⟨297517994051101691368661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3173525269878418041265717 297517994051101691368661)
                  ·
                    rfl

theorem cell20_651841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_651841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651841 prefixEnd_651841 := by exact prefixLift 651841
  have htrace : WordTrace (prefixWord ++ tailWord_651841) baseStart_651841 baseEnd_651841 := by
    simpa [prefixWord, tailWord_651841, baseEnd_651841] using wordTrace_append hprefix tailTrace_651841
  have hstable : (prefixWord ++ tailWord_651841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651841).length < 2 ^ (prefixWord ++ tailWord_651841).sum := by decide
  have hdescent : baseEnd_651841 < baseStart_651841 := by decide
  rcases family_descends (prefixWord ++ tailWord_651841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651900 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_651900 : Nat := 118140960795 + 651900 * 2 ^ 59
def prefixEnd_651900 : Nat := 4983230072969 + 3 ^ 40 * 651900 * 2
def baseEnd_651900 : Nat := 297544923258759708401753

theorem tailTrace_651900 : CollatzResearch.WordTrace tailWord_651900 prefixEnd_651900 297544923258759708401753 := by
  unfold tailWord_651900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888373169142555250612577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15851164225523407000816769 11888373169142555250612577)
  ·
    refine ⟨8916279876856916437959433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11888373169142555250612577 8916279876856916437959433)
    ·
      refine ⟨6687209907642687328469575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8916279876856916437959433 6687209907642687328469575)
      ·
        refine ⟨10030814861464030992704363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687209907642687328469575 10030814861464030992704363)
        ·
          refine ⟨15046222292196046489056545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10030814861464030992704363 15046222292196046489056545)
          ·
            refine ⟨11284666719147034866792409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15046222292196046489056545 11284666719147034866792409)
            ·
              refine ⟨8463500039360276150094307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11284666719147034866792409 8463500039360276150094307)
              ·
                refine ⟨12695250059040414225141461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463500039360276150094307 12695250059040414225141461)
                ·
                  refine ⟨297544923258759708401753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12695250059040414225141461 297544923258759708401753)
                  ·
                    rfl

theorem cell20_651900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_651900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651900 prefixEnd_651900 := by exact prefixLift 651900
  have htrace : WordTrace (prefixWord ++ tailWord_651900) baseStart_651900 baseEnd_651900 := by
    simpa [prefixWord, tailWord_651900, baseEnd_651900] using wordTrace_append hprefix tailTrace_651900
  have hstable : (prefixWord ++ tailWord_651900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651900).length < 2 ^ (prefixWord ++ tailWord_651900).sum := by decide
  have hdescent : baseEnd_651900 < baseStart_651900 := by decide
  rcases family_descends (prefixWord ++ tailWord_651900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651906 : List Nat := [3, 4, 3, 1, 1, 8]
def baseStart_651906 : Nat := 118140960795 + 651906 * 2 ^ 59
def prefixEnd_651906 : Nat := 4983230072969 + 3 ^ 40 * 651906 * 2
def baseEnd_651906 : Nat := 11020283771194457563027

theorem tailTrace_651906 : CollatzResearch.WordTrace tailWord_651906 prefixEnd_651906 11020283771194457563027 := by
  unfold tailWord_651906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944241294065843381485893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15851310117508915683962381 5944241294065843381485893)
  ·
    refine ⟨1114545242637345634028605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5944241294065843381485893 1114545242637345634028605)
    ·
      refine ⟨417954465989004612760727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1114545242637345634028605 417954465989004612760727)
      ·
        refine ⟨626931698983506919141091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417954465989004612760727 626931698983506919141091)
        ·
          refine ⟨940397548475260378711637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626931698983506919141091 940397548475260378711637)
          ·
            refine ⟨11020283771194457563027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 940397548475260378711637 11020283771194457563027)
            ·
              rfl

theorem cell20_651906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 8].length) (baseStart_651906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651906 prefixEnd_651906 := by exact prefixLift 651906
  have htrace : WordTrace (prefixWord ++ tailWord_651906) baseStart_651906 baseEnd_651906 := by
    simpa [prefixWord, tailWord_651906, baseEnd_651906] using wordTrace_append hprefix tailTrace_651906
  have hstable : (prefixWord ++ tailWord_651906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651906).length < 2 ^ (prefixWord ++ tailWord_651906).sum := by decide
  have hdescent : baseEnd_651906 < baseStart_651906 := by decide
  rcases family_descends (prefixWord ++ tailWord_651906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651934 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_651934 : Nat := 118140960795 + 651934 * 2 ^ 59
def prefixEnd_651934 : Nat := 4983230072969 + 3 ^ 40 * 651934 * 2
def baseEnd_651934 : Nat := 297560441785206701268281

theorem tailTrace_651934 : CollatzResearch.WordTrace tailWord_651934 prefixEnd_651934 297560441785206701268281 := by
  unfold tailWord_651934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972248302520241788495357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15851990946774622871975237 2972248302520241788495357)
  ·
    refine ⟨1114593113445090670685759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2972248302520241788495357 1114593113445090670685759)
    ·
      refine ⟨1671889670167636006028639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114593113445090670685759 1671889670167636006028639)
      ·
        refine ⟨2507834505251454009042959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671889670167636006028639 2507834505251454009042959)
        ·
          refine ⟨3761751757877181013564439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507834505251454009042959 3761751757877181013564439)
          ·
            refine ⟨5642627636815771520346659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761751757877181013564439 5642627636815771520346659)
            ·
              refine ⟨8463941455223657280519989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642627636815771520346659 8463941455223657280519989)
              ·
                refine ⟨793494511427217870048749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8463941455223657280519989 793494511427217870048749)
                ·
                  refine ⟨297560441785206701268281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793494511427217870048749 297560441785206701268281)
                  ·
                    rfl

theorem cell20_651934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_651934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651934 prefixEnd_651934 := by exact prefixLift 651934
  have htrace : WordTrace (prefixWord ++ tailWord_651934) baseStart_651934 baseEnd_651934 := by
    simpa [prefixWord, tailWord_651934, baseEnd_651934] using wordTrace_append hprefix tailTrace_651934
  have hstable : (prefixWord ++ tailWord_651934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651934).length < 2 ^ (prefixWord ++ tailWord_651934).sum := by decide
  have hdescent : baseEnd_651934 < baseStart_651934 := by decide
  rcases family_descends (prefixWord ++ tailWord_651934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651945 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_651945 : Nat := 118140960795 + 651945 * 2 ^ 59
def prefixEnd_651945 : Nat := 4983230072969 + 3 ^ 40 * 651945 * 2
def baseEnd_651945 : Nat := 297565462484939551901569

theorem tailTrace_651945 : CollatzResearch.WordTrace tailWord_651945 prefixEnd_651945 297565462484939551901569 := by
  unfold tailWord_651945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778387623122083186613289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15852258415414722124408859 23778387623122083186613289)
  ·
    refine ⟨17833790717341562389959967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23778387623122083186613289 17833790717341562389959967)
    ·
      refine ⟨26750686076012343584939951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17833790717341562389959967 26750686076012343584939951)
      ·
        refine ⟨40126029114018515377409927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26750686076012343584939951 40126029114018515377409927)
        ·
          refine ⟨60189043671027773066114891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40126029114018515377409927 60189043671027773066114891)
          ·
            refine ⟨90283565506541659599172337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60189043671027773066114891 90283565506541659599172337)
            ·
              refine ⟨67712674129906244699379253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90283565506541659599172337 67712674129906244699379253)
              ·
                refine ⟨6348063199678710440566805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67712674129906244699379253 6348063199678710440566805)
                ·
                  refine ⟨297565462484939551901569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6348063199678710440566805 297565462484939551901569)
                  ·
                    rfl

theorem cell20_651945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_651945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651945 prefixEnd_651945 := by exact prefixLift 651945
  have htrace : WordTrace (prefixWord ++ tailWord_651945) baseStart_651945 baseEnd_651945 := by
    simpa [prefixWord, tailWord_651945, baseEnd_651945] using wordTrace_append hprefix tailTrace_651945
  have hstable : (prefixWord ++ tailWord_651945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651945).length < 2 ^ (prefixWord ++ tailWord_651945).sum := by decide
  have hdescent : baseEnd_651945 < baseStart_651945 := by decide
  rcases family_descends (prefixWord ++ tailWord_651945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651972 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_651972 : Nat := 118140960795 + 651972 * 2 ^ 59
def prefixEnd_651972 : Nat := 4983230072969 + 3 ^ 40 * 651972 * 2
def baseEnd_651972 : Nat := 297577786020647458001459

theorem tailTrace_651972 : CollatzResearch.WordTrace tailWord_651972 prefixEnd_651972 297577786020647458001459 := by
  unfold tailWord_651972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889686197012133398923085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15852914929349511198564113 11889686197012133398923085)
  ·
    refine ⟨4458632323879550024596157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11889686197012133398923085 4458632323879550024596157)
    ·
      refine ⟨1671987121454831259223559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4458632323879550024596157 1671987121454831259223559)
      ·
        refine ⟨2507980682182246888835339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671987121454831259223559 2507980682182246888835339)
        ·
          refine ⟨3761971023273370333253009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507980682182246888835339 3761971023273370333253009)
          ·
            refine ⟨2821478267455027749939757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3761971023273370333253009 2821478267455027749939757)
            ·
              refine ⟨1058054350295635406227409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821478267455027749939757 1058054350295635406227409)
              ·
                refine ⟨793540762721726554670557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058054350295635406227409 793540762721726554670557)
                ·
                  refine ⟨297577786020647458001459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793540762721726554670557 297577786020647458001459)
                  ·
                    rfl

theorem cell20_651972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_651972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_651972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_651972 prefixEnd_651972 := by exact prefixLift 651972
  have htrace : WordTrace (prefixWord ++ tailWord_651972) baseStart_651972 baseEnd_651972 := by
    simpa [prefixWord, tailWord_651972, baseEnd_651972] using wordTrace_append hprefix tailTrace_651972
  have hstable : (prefixWord ++ tailWord_651972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651972).length < 2 ^ (prefixWord ++ tailWord_651972).sum := by decide
  have hdescent : baseEnd_651972 < baseStart_651972 := by decide
  rcases family_descends (prefixWord ++ tailWord_651972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652003 : List Nat := [1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_652003 : Nat := 118140960795 + 652003 * 2 ^ 59
def prefixEnd_652003 : Nat := 4983230072969 + 3 ^ 40 * 652003 * 2
def baseEnd_652003 : Nat := 99197311755116375989333

theorem tailTrace_652003 : CollatzResearch.WordTrace tailWord_652003 prefixEnd_652003 99197311755116375989333 := by
  unfold tailWord_652003
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780503056911959092224663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15853668704607972728149775 23780503056911959092224663)
  ·
    refine ⟨35670754585367938638336995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23780503056911959092224663 35670754585367938638336995)
    ·
      refine ⟨53506131878051907957505493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35670754585367938638336995 53506131878051907957505493)
      ·
        refine ⟨1254049965891841592754035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53506131878051907957505493 1254049965891841592754035)
        ·
          refine ⟨1881074948837762389131053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254049965891841592754035 1881074948837762389131053)
          ·
            refine ⟨705403105814160895924145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1881074948837762389131053 705403105814160895924145)
            ·
              refine ⟨529052329360620671943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705403105814160895924145 529052329360620671943109)
              ·
                refine ⟨99197311755116375989333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529052329360620671943109 99197311755116375989333)
                ·
                  rfl

theorem cell20_652003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_652003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652003 prefixEnd_652003 := by exact prefixLift 652003
  have htrace : WordTrace (prefixWord ++ tailWord_652003) baseStart_652003 baseEnd_652003 := by
    simpa [prefixWord, tailWord_652003, baseEnd_652003] using wordTrace_append hprefix tailTrace_652003
  have hstable : (prefixWord ++ tailWord_652003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652003).length < 2 ^ (prefixWord ++ tailWord_652003).sum := by decide
  have hdescent : baseEnd_652003 < baseStart_652003 := by decide
  rcases family_descends (prefixWord ++ tailWord_652003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652020 : List Nat := [2, 6, 1, 1, 2, 2, 6]
def baseStart_652020 : Nat := 118140960795 + 652020 * 2 ^ 59
def prefixEnd_652020 : Nat := 4983230072969 + 3 ^ 40 * 652020 * 2
def baseEnd_652020 : Nat := 33066632725396958266807

theorem tailTrace_652020 : CollatzResearch.WordTrace tailWord_652020 prefixEnd_652020 33066632725396958266807 := by
  unfold tailWord_652020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11890561548925185497796757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15854082065233580663729009 11890561548925185497796757)
  ·
    refine ⟨557370072605868070209223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11890561548925185497796757 557370072605868070209223)
    ·
      refine ⟨836055108908802105313835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557370072605868070209223 836055108908802105313835)
      ·
        refine ⟨1254082663363203157970753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836055108908802105313835 1254082663363203157970753)
        ·
          refine ⟨940561997522402368478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254082663363203157970753 940561997522402368478065)
          ·
            refine ⟨705421498141801776358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940561997522402368478065 705421498141801776358549)
            ·
              refine ⟨33066632725396958266807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705421498141801776358549 33066632725396958266807)
              ·
                rfl

theorem cell20_652020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_652020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652020 prefixEnd_652020 := by exact prefixLift 652020
  have htrace : WordTrace (prefixWord ++ tailWord_652020) baseStart_652020 baseEnd_652020 := by
    simpa [prefixWord, tailWord_652020, baseEnd_652020] using wordTrace_append hprefix tailTrace_652020
  have hstable : (prefixWord ++ tailWord_652020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652020).length < 2 ^ (prefixWord ++ tailWord_652020).sum := by decide
  have hdescent : baseEnd_652020 < baseStart_652020 := by decide
  rcases family_descends (prefixWord ++ tailWord_652020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652034 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_652034 : Nat := 118140960795 + 652034 * 2 ^ 59
def prefixEnd_652034 : Nat := 4983230072969 + 3 ^ 40 * 652034 * 2
def baseEnd_652034 : Nat := 297606084510050797934539

theorem tailTrace_652034 : CollatzResearch.WordTrace tailWord_652034 prefixEnd_652034 297606084510050797934539 := by
  unfold tailWord_652034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945408429949912846650789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15854422479866434257735437 5945408429949912846650789)
  ·
    refine ⟨1114764080615608658747023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5945408429949912846650789 1114764080615608658747023)
    ·
      refine ⟨1672146120923412988120535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114764080615608658747023 1672146120923412988120535)
      ·
        refine ⟨2508219181385119482180803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672146120923412988120535 2508219181385119482180803)
        ·
          refine ⟨3762328772077679223271205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508219181385119482180803 3762328772077679223271205)
          ·
            refine ⟨705436644764564854363351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3762328772077679223271205 705436644764564854363351)
            ·
              refine ⟨1058154967146847281545027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705436644764564854363351 1058154967146847281545027)
              ·
                refine ⟨1587232450720270922317541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058154967146847281545027 1587232450720270922317541)
                ·
                  refine ⟨297606084510050797934539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587232450720270922317541 297606084510050797934539)
                  ·
                    rfl

theorem cell20_652034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_652034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652034 prefixEnd_652034 := by exact prefixLift 652034
  have htrace : WordTrace (prefixWord ++ tailWord_652034) baseStart_652034 baseEnd_652034 := by
    simpa [prefixWord, tailWord_652034, baseEnd_652034] using wordTrace_append hprefix tailTrace_652034
  have hstable : (prefixWord ++ tailWord_652034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652034).length < 2 ^ (prefixWord ++ tailWord_652034).sum := by decide
  have hdescent : baseEnd_652034 < baseStart_652034 := by decide
  rcases family_descends (prefixWord ++ tailWord_652034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652114 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_652114 : Nat := 118140960795 + 652114 * 2 ^ 59
def prefixEnd_652114 : Nat := 4983230072969 + 3 ^ 40 * 652114 * 2
def baseEnd_652114 : Nat := 297642598689926075267545

theorem tailTrace_652114 : CollatzResearch.WordTrace tailWord_652114 prefixEnd_652114 297642598689926075267545 := by
  unfold tailWord_652114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946137889877456262378849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15856367706339883366343597 5946137889877456262378849)
  ·
    refine ⟨4459603417408092196784137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5946137889877456262378849 4459603417408092196784137)
    ·
      refine ⟨3344702563056069147588103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4459603417408092196784137 3344702563056069147588103)
      ·
        refine ⟨5017053844584103721382155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344702563056069147588103 5017053844584103721382155)
        ·
          refine ⟨7525580766876155582073233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017053844584103721382155 7525580766876155582073233)
          ·
            refine ⟨5644185575157116686554925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525580766876155582073233 5644185575157116686554925)
            ·
              refine ⟨2116569590683918757458097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5644185575157116686554925 2116569590683918757458097)
              ·
                refine ⟨1587427193012939068093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116569590683918757458097 1587427193012939068093573)
                ·
                  refine ⟨297642598689926075267545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587427193012939068093573 297642598689926075267545)
                  ·
                    rfl

theorem cell20_652114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_652114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652114 prefixEnd_652114 := by exact prefixLift 652114
  have htrace : WordTrace (prefixWord ++ tailWord_652114) baseStart_652114 baseEnd_652114 := by
    simpa [prefixWord, tailWord_652114, baseEnd_652114] using wordTrace_append hprefix tailTrace_652114
  have hstable : (prefixWord ++ tailWord_652114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652114).length < 2 ^ (prefixWord ++ tailWord_652114).sum := by decide
  have hdescent : baseEnd_652114 < baseStart_652114 := by decide
  rcases family_descends (prefixWord ++ tailWord_652114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652128 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_652128 : Nat := 118140960795 + 652128 * 2 ^ 59
def prefixEnd_652128 : Nat := 4983230072969 + 3 ^ 40 * 652128 * 2
def baseEnd_652128 : Nat := 297648988671404248800821

theorem tailTrace_652128 : CollatzResearch.WordTrace tailWord_652128 prefixEnd_652128 297648988671404248800821 := by
  unfold tailWord_652128
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892531090729552720262519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15856708120972736960350025 11892531090729552720262519)
  ·
    refine ⟨17838796636094329080393779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11892531090729552720262519 17838796636094329080393779)
    ·
      refine ⟨26758194954141493620590669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17838796636094329080393779 26758194954141493620590669)
      ·
        refine ⟨10034323107803060107721501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26758194954141493620590669 10034323107803060107721501)
        ·
          refine ⟨3762871165426147540395563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10034323107803060107721501 3762871165426147540395563)
          ·
            refine ⟨5644306748139221310593345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762871165426147540395563 5644306748139221310593345)
            ·
              refine ⟨4233230061104415982945009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5644306748139221310593345 4233230061104415982945009)
              ·
                refine ⟨3174922545828311987208757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233230061104415982945009 3174922545828311987208757)
                ·
                  refine ⟨297648988671404248800821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3174922545828311987208757 297648988671404248800821)
                  ·
                    rfl

theorem cell20_652128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_652128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652128 prefixEnd_652128 := by exact prefixLift 652128
  have htrace : WordTrace (prefixWord ++ tailWord_652128) baseStart_652128 baseEnd_652128 := by
    simpa [prefixWord, tailWord_652128, baseEnd_652128] using wordTrace_append hprefix tailTrace_652128
  have hstable : (prefixWord ++ tailWord_652128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652128).length < 2 ^ (prefixWord ++ tailWord_652128).sum := by decide
  have hdescent : baseEnd_652128 < baseStart_652128 := by decide
  rcases family_descends (prefixWord ++ tailWord_652128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652131 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 2]
def baseStart_652131 : Nat := 118140960795 + 652131 * 2 ^ 59
def prefixEnd_652131 : Nat := 4983230072969 + 3 ^ 40 * 652131 * 2
def baseEnd_652131 : Nat := 297650357953149571700809

theorem tailTrace_652131 : CollatzResearch.WordTrace tailWord_652131 prefixEnd_652131 297650357953149571700809 := by
  unfold tailWord_652131
  simp only [CollatzResearch.WordTrace]
  refine ⟨23785171600448236952884247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15856781066965491301922831 23785171600448236952884247)
  ·
    refine ⟨35677757400672355429326371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23785171600448236952884247 35677757400672355429326371)
    ·
      refine ⟨53516636101008533143989557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35677757400672355429326371 53516636101008533143989557)
      ·
        refine ⟨5017184634469549982249021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53516636101008533143989557 5017184634469549982249021)
        ·
          refine ⟨1881444237926081243343383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5017184634469549982249021 1881444237926081243343383)
          ·
            refine ⟨2822166356889121865015075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881444237926081243343383 2822166356889121865015075)
            ·
              refine ⟨4233249535333682797522613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822166356889121865015075 4233249535333682797522613)
              ·
                refine ⟨396867143937532762267745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4233249535333682797522613 396867143937532762267745)
                ·
                  refine ⟨297650357953149571700809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396867143937532762267745 297650357953149571700809)
                  ·
                    rfl

theorem cell20_652131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2].length) (baseStart_652131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652131 prefixEnd_652131 := by exact prefixLift 652131
  have htrace : WordTrace (prefixWord ++ tailWord_652131) baseStart_652131 baseEnd_652131 := by
    simpa [prefixWord, tailWord_652131, baseEnd_652131] using wordTrace_append hprefix tailTrace_652131
  have hstable : (prefixWord ++ tailWord_652131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652131).length < 2 ^ (prefixWord ++ tailWord_652131).sum := by decide
  have hdescent : baseEnd_652131 < baseStart_652131 := by decide
  rcases family_descends (prefixWord ++ tailWord_652131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652145 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_652145 : Nat := 118140960795 + 652145 * 2 ^ 59
def prefixEnd_652145 : Nat := 4983230072969 + 3 ^ 40 * 652145 * 2
def baseEnd_652145 : Nat := 297656747934627745234085

theorem tailTrace_652145 : CollatzResearch.WordTrace tailWord_652145 prefixEnd_652145 297656747934627745234085 := by
  unfold tailWord_652145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23785682222397517343893889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15857121481598344895929259 23785682222397517343893889)
  ·
    refine ⟨17839261666798138007920417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23785682222397517343893889 17839261666798138007920417)
    ·
      refine ⟨13379446250098603505940313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17839261666798138007920417 13379446250098603505940313)
      ·
        refine ⟨10034584687573952629455235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13379446250098603505940313 10034584687573952629455235)
        ·
          refine ⟨15051877031360928944182853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10034584687573952629455235 15051877031360928944182853)
          ·
            refine ⟨2822226943380174177034285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15051877031360928944182853 2822226943380174177034285)
            ·
              refine ⟨1058335103767565316387857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2822226943380174177034285 1058335103767565316387857)
              ·
                refine ⟨793751327825673987290893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058335103767565316387857 793751327825673987290893)
                ·
                  refine ⟨297656747934627745234085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793751327825673987290893 297656747934627745234085)
                  ·
                    rfl

theorem cell20_652145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_652145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652145 prefixEnd_652145 := by exact prefixLift 652145
  have htrace : WordTrace (prefixWord ++ tailWord_652145) baseStart_652145 baseEnd_652145 := by
    simpa [prefixWord, tailWord_652145, baseEnd_652145] using wordTrace_append hprefix tailTrace_652145
  have hstable : (prefixWord ++ tailWord_652145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652145).length < 2 ^ (prefixWord ++ tailWord_652145).sum := by decide
  have hdescent : baseEnd_652145 < baseStart_652145 := by decide
  rcases family_descends (prefixWord ++ tailWord_652145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652158 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_652158 : Nat := 118140960795 + 652158 * 2 ^ 59
def prefixEnd_652158 : Nat := 4983230072969 + 3 ^ 40 * 652158 * 2
def baseEnd_652158 : Nat := 297662681488857477800699

theorem tailTrace_652158 : CollatzResearch.WordTrace tailWord_652158 prefixEnd_652158 297662681488857477800699 := by
  unfold tailWord_652158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973269546418802570514641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15857437580900280376078085 2973269546418802570514641)
  ·
    refine ⟨2229952159814101927885981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2973269546418802570514641 2229952159814101927885981)
    ·
      refine ⟨836232059930288222957243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2229952159814101927885981 836232059930288222957243)
      ·
        refine ⟨1254348089895432334435865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836232059930288222957243 1254348089895432334435865)
        ·
          refine ⟨940761067421574250826899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254348089895432334435865 940761067421574250826899)
          ·
            refine ⟨1411141601132361376240349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940761067421574250826899 1411141601132361376240349)
            ·
              refine ⟨529178100424635516090131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411141601132361376240349 529178100424635516090131)
              ·
                refine ⟨793767150636953274135197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529178100424635516090131 793767150636953274135197)
                ·
                  refine ⟨297662681488857477800699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793767150636953274135197 297662681488857477800699)
                  ·
                    rfl

theorem cell20_652158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_652158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652158 prefixEnd_652158 := by exact prefixLift 652158
  have htrace : WordTrace (prefixWord ++ tailWord_652158) baseStart_652158 baseEnd_652158 := by
    simpa [prefixWord, tailWord_652158, baseEnd_652158] using wordTrace_append hprefix tailTrace_652158
  have hstable : (prefixWord ++ tailWord_652158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652158).length < 2 ^ (prefixWord ++ tailWord_652158).sum := by decide
  have hdescent : baseEnd_652158 < baseStart_652158 := by decide
  rcases family_descends (prefixWord ++ tailWord_652158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652182 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_652182 : Nat := 118140960795 + 652182 * 2 ^ 59
def prefixEnd_652182 : Nat := 4983230072969 + 3 ^ 40 * 652182 * 2
def baseEnd_652182 : Nat := 297673635742820061000601

theorem tailTrace_652182 : CollatzResearch.WordTrace tailWord_652182 prefixEnd_652182 297673635742820061000601 := by
  unfold tailWord_652182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486689482703967041436925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15858021148842315108660533 1486689482703967041436925)
  ·
    refine ⟨557508556013987640538847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1486689482703967041436925 557508556013987640538847)
    ·
      refine ⟨836262834020981460808271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557508556013987640538847 836262834020981460808271)
      ·
        refine ⟨1254394251031472191212407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836262834020981460808271 1254394251031472191212407)
        ·
          refine ⟨1881591376547208286818611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254394251031472191212407 1881591376547208286818611)
          ·
            refine ⟨2822387064820812430227917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881591376547208286818611 2822387064820812430227917)
            ·
              refine ⟨1058395149307804661335469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2822387064820812430227917 1058395149307804661335469)
              ·
                refine ⟨396898180990426748000801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058395149307804661335469 396898180990426748000801)
                ·
                  refine ⟨297673635742820061000601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396898180990426748000801 297673635742820061000601)
                  ·
                    rfl

theorem cell20_652182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_652182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652182 prefixEnd_652182 := by exact prefixLift 652182
  have htrace : WordTrace (prefixWord ++ tailWord_652182) baseStart_652182 baseEnd_652182 := by
    simpa [prefixWord, tailWord_652182, baseEnd_652182] using wordTrace_append hprefix tailTrace_652182
  have hstable : (prefixWord ++ tailWord_652182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652182).length < 2 ^ (prefixWord ++ tailWord_652182).sum := by decide
  have hdescent : baseEnd_652182 < baseStart_652182 := by decide
  rcases family_descends (prefixWord ++ tailWord_652182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652211 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_652211 : Nat := 118140960795 + 652211 * 2 ^ 59
def prefixEnd_652211 : Nat := 4983230072969 + 3 ^ 40 * 652211 * 2
def baseEnd_652211 : Nat := 297686872133024849033815

theorem tailTrace_652211 : CollatzResearch.WordTrace tailWord_652211 prefixEnd_652211 297686872133024849033815 := by
  unfold tailWord_652211
  simp only [CollatzResearch.WordTrace]
  refine ⟨23788089440158410615796487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15858726293438940410530991 23788089440158410615796487)
  ·
    refine ⟨35682134160237615923694731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23788089440158410615796487 35682134160237615923694731)
    ·
      refine ⟨53523201240356423885542097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35682134160237615923694731 53523201240356423885542097)
      ·
        refine ⟨40142400930267317914156573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53523201240356423885542097 40142400930267317914156573)
        ·
          refine ⟨15053400348850244217808715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40142400930267317914156573 15053400348850244217808715)
          ·
            refine ⟨22580100523275366326713073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15053400348850244217808715 22580100523275366326713073)
            ·
              refine ⟨16935075392456524745034805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22580100523275366326713073 16935075392456524745034805)
              ·
                refine ⟨1587663318042799194847013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16935075392456524745034805 1587663318042799194847013)
                ·
                  refine ⟨297686872133024849033815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587663318042799194847013 297686872133024849033815)
                  ·
                    rfl

theorem cell20_652211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_652211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652211 prefixEnd_652211 := by exact prefixLift 652211
  have htrace : WordTrace (prefixWord ++ tailWord_652211) baseStart_652211 baseEnd_652211 := by
    simpa [prefixWord, tailWord_652211, baseEnd_652211] using wordTrace_append hprefix tailTrace_652211
  have hstable : (prefixWord ++ tailWord_652211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652211).length < 2 ^ (prefixWord ++ tailWord_652211).sum := by decide
  have hdescent : baseEnd_652211 < baseStart_652211 := by decide
  rcases family_descends (prefixWord ++ tailWord_652211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652258 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_652258 : Nat := 118140960795 + 652258 * 2 ^ 59
def prefixEnd_652258 : Nat := 4983230072969 + 3 ^ 40 * 652258 * 2
def baseEnd_652258 : Nat := 297708324213701574466957

theorem tailTrace_652258 : CollatzResearch.WordTrace tailWord_652258 prefixEnd_652258 297708324213701574466957 := by
  unfold tailWord_652258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947450917747034410689357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15859869113992091761838285 5947450917747034410689357)
  ·
    refine ⟨2230294094155137904008509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5947450917747034410689357 2230294094155137904008509)
    ·
      refine ⟨836360285308176714003191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2230294094155137904008509 836360285308176714003191)
      ·
        refine ⟨1254540427962265071004787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836360285308176714003191 1254540427962265071004787)
        ·
          refine ⟨1881810641943397606507181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254540427962265071004787 1881810641943397606507181)
          ·
            refine ⟨705678990728774102440193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1881810641943397606507181 705678990728774102440193)
            ·
              refine ⟨529259243046580576830145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705678990728774102440193 529259243046580576830145)
              ·
                refine ⟨396944432284935432622609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529259243046580576830145 396944432284935432622609)
                ·
                  refine ⟨297708324213701574466957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396944432284935432622609 297708324213701574466957)
                  ·
                    rfl

theorem cell20_652258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_652258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652258 prefixEnd_652258 := by exact prefixLift 652258
  have htrace : WordTrace (prefixWord ++ tailWord_652258) baseStart_652258 baseEnd_652258 := by
    simpa [prefixWord, tailWord_652258, baseEnd_652258] using wordTrace_append hprefix tailTrace_652258
  have hstable : (prefixWord ++ tailWord_652258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652258).length < 2 ^ (prefixWord ++ tailWord_652258).sum := by decide
  have hdescent : baseEnd_652258 < baseStart_652258 := by decide
  rcases family_descends (prefixWord ++ tailWord_652258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652259 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_652259 : Nat := 118140960795 + 652259 * 2 ^ 59
def prefixEnd_652259 : Nat := 4983230072969 + 3 ^ 40 * 652259 * 2
def baseEnd_652259 : Nat := 297708780640950015433619

theorem tailTrace_652259 : CollatzResearch.WordTrace tailWord_652259 prefixEnd_652259 297708780640950015433619 := by
  unfold tailWord_652259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789840143984514813543831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15859893429323009875695887 23789840143984514813543831)
  ·
    refine ⟨35684760215976772220315747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23789840143984514813543831 35684760215976772220315747)
    ·
      refine ⟨53527140323965158330473621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35684760215976772220315747 53527140323965158330473621)
      ·
        refine ⟨2509084702685866796740951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53527140323965158330473621 2509084702685866796740951)
        ·
          refine ⟨3763627054028800195111427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509084702685866796740951 3763627054028800195111427)
          ·
            refine ⟨5645440581043200292667141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763627054028800195111427 5645440581043200292667141)
            ·
              refine ⟨1058520108945600054875089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5645440581043200292667141 1058520108945600054875089)
              ·
                refine ⟨793890081709200041156317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058520108945600054875089 793890081709200041156317)
                ·
                  refine ⟨297708780640950015433619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793890081709200041156317 297708780640950015433619)
                  ·
                    rfl

theorem cell20_652259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_652259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652259 prefixEnd_652259 := by exact prefixLift 652259
  have htrace : WordTrace (prefixWord ++ tailWord_652259) baseStart_652259 baseEnd_652259 := by
    simpa [prefixWord, tailWord_652259, baseEnd_652259] using wordTrace_append hprefix tailTrace_652259
  have hstable : (prefixWord ++ tailWord_652259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652259).length < 2 ^ (prefixWord ++ tailWord_652259).sum := by decide
  have hdescent : baseEnd_652259 < baseStart_652259 := by decide
  rcases family_descends (prefixWord ++ tailWord_652259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652273 : List Nat := [1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_652273 : Nat := 118140960795 + 652273 * 2 ^ 59
def prefixEnd_652273 : Nat := 4983230072969 + 3 ^ 40 * 652273 * 2
def baseEnd_652273 : Nat := 99238390207476062988965

theorem tailTrace_652273 : CollatzResearch.WordTrace tailWord_652273 prefixEnd_652273 99238390207476062988965 := by
  unfold tailWord_652273
  simp only [CollatzResearch.WordTrace]
  refine ⟨23790350765933795204553473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15860233843955863469702315 23790350765933795204553473)
  ·
    refine ⟨17842763074450346403415105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23790350765933795204553473 17842763074450346403415105)
    ·
      refine ⟨13382072305837759802561329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17842763074450346403415105 13382072305837759802561329)
      ·
        refine ⟨10036554229378319851920997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13382072305837759802561329 10036554229378319851920997)
        ·
          refine ⟨1881853918008434972235187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10036554229378319851920997 1881853918008434972235187)
          ·
            refine ⟨2822780877012652458352781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881853918008434972235187 2822780877012652458352781)
            ·
              refine ⟨1058542828879744671882293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2822780877012652458352781 1058542828879744671882293)
              ·
                refine ⟨99238390207476062988965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1058542828879744671882293 99238390207476062988965)
                ·
                  rfl

theorem cell20_652273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_652273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652273 prefixEnd_652273 := by exact prefixLift 652273
  have htrace : WordTrace (prefixWord ++ tailWord_652273) baseStart_652273 baseEnd_652273 := by
    simpa [prefixWord, tailWord_652273, baseEnd_652273] using wordTrace_append hprefix tailTrace_652273
  have hstable : (prefixWord ++ tailWord_652273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652273).length < 2 ^ (prefixWord ++ tailWord_652273).sum := by decide
  have hdescent : baseEnd_652273 < baseStart_652273 := by decide
  rcases family_descends (prefixWord ++ tailWord_652273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652311 : List Nat := [1, 1, 3, 5, 1, 2, 7]
def baseStart_652311 : Nat := 118140960795 + 652311 * 2 ^ 59
def prefixEnd_652311 : Nat := 4983230072969 + 3 ^ 40 * 652311 * 2
def baseEnd_652311 : Nat := 33081390539763216188897

theorem tailTrace_652311 : CollatzResearch.WordTrace tailWord_652311 prefixEnd_652311 33081390539763216188897 := by
  unfold tailWord_652311
  simp only [CollatzResearch.WordTrace]
  refine ⟨23791736739796127694436787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15861157826530751796291191 23791736739796127694436787)
  ·
    refine ⟨35687605109694191541655181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23791736739796127694436787 35687605109694191541655181)
    ·
      refine ⟨13382851916135321828120693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35687605109694191541655181 13382851916135321828120693)
      ·
        refine ⟨1254642367137686421386315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13382851916135321828120693 1254642367137686421386315)
        ·
          refine ⟨1881963550706529632079473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254642367137686421386315 1881963550706529632079473)
          ·
            refine ⟨1411472663029897224059605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881963550706529632079473 1411472663029897224059605)
            ·
              refine ⟨33081390539763216188897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1411472663029897224059605 33081390539763216188897)
              ·
                rfl

theorem cell20_652311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_652311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652311 prefixEnd_652311 := by exact prefixLift 652311
  have htrace : WordTrace (prefixWord ++ tailWord_652311) baseStart_652311 baseEnd_652311 := by
    simpa [prefixWord, tailWord_652311, baseEnd_652311] using wordTrace_append hprefix tailTrace_652311
  have hstable : (prefixWord ++ tailWord_652311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652311).length < 2 ^ (prefixWord ++ tailWord_652311).sum := by decide
  have hdescent : baseEnd_652311 < baseStart_652311 := by decide
  rcases family_descends (prefixWord ++ tailWord_652311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652321 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 2]
def baseStart_652321 : Nat := 118140960795 + 652321 * 2 ^ 59
def prefixEnd_652321 : Nat := 4983230072969 + 3 ^ 40 * 652321 * 2
def baseEnd_652321 : Nat := 297737079130353355366699

theorem tailTrace_652321 : CollatzResearch.WordTrace tailWord_652321 prefixEnd_652321 297737079130353355366699 := by
  unfold tailWord_652321
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792101469759899402300817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15861400979839932934867211 23792101469759899402300817)
  ·
    refine ⟨17844076102319924551725613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23792101469759899402300817 17844076102319924551725613)
    ·
      refine ⟨6691528538369971706897105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17844076102319924551725613 6691528538369971706897105)
      ·
        refine ⟨5018646403777478780172829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6691528538369971706897105 5018646403777478780172829)
        ·
          refine ⟨1881992401416554542564811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5018646403777478780172829 1881992401416554542564811)
          ·
            refine ⟨2822988602124831813847217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881992401416554542564811 2822988602124831813847217)
            ·
              refine ⟨2117241451593623860385413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822988602124831813847217 2117241451593623860385413)
              ·
                refine ⟨396982772173804473822265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2117241451593623860385413 396982772173804473822265)
                ·
                  refine ⟨297737079130353355366699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396982772173804473822265 297737079130353355366699)
                  ·
                    rfl

theorem cell20_652321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_652321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652321 prefixEnd_652321 := by exact prefixLift 652321
  have htrace : WordTrace (prefixWord ++ tailWord_652321) baseStart_652321 baseEnd_652321 := by
    simpa [prefixWord, tailWord_652321, baseEnd_652321] using wordTrace_append hprefix tailTrace_652321
  have hstable : (prefixWord ++ tailWord_652321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652321).length < 2 ^ (prefixWord ++ tailWord_652321).sum := by decide
  have hdescent : baseEnd_652321 < baseStart_652321 := by decide
  rcases family_descends (prefixWord ++ tailWord_652321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652332 : List Nat := [2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_652332 : Nat := 118140960795 + 652332 * 2 ^ 59
def prefixEnd_652332 : Nat := 4983230072969 + 3 ^ 40 * 652332 * 2
def baseEnd_652332 : Nat := 99247366610028735333329

theorem tailTrace_652332 : CollatzResearch.WordTrace tailWord_652332 prefixEnd_652332 99247366610028735333329 := by
  unfold tailWord_652332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896251336360024140475625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15861668448480032187300833 11896251336360024140475625)
  ·
    refine ⟨8922188502270018105356719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11896251336360024140475625 8922188502270018105356719)
    ·
      refine ⟨13383282753405027158035079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922188502270018105356719 13383282753405027158035079)
      ·
        refine ⟨20074924130107540737052619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13383282753405027158035079 20074924130107540737052619)
        ·
          refine ⟨30112386195161311105578929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20074924130107540737052619 30112386195161311105578929)
          ·
            refine ⟨22584289646370983329184197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30112386195161311105578929 22584289646370983329184197)
            ·
              refine ⟨4234554308694559374222037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22584289646370983329184197 4234554308694559374222037)
              ·
                refine ⟨99247366610028735333329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4234554308694559374222037 99247366610028735333329)
                ·
                  rfl

theorem cell20_652332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_652332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652332 prefixEnd_652332 := by exact prefixLift 652332
  have htrace : WordTrace (prefixWord ++ tailWord_652332) baseStart_652332 baseEnd_652332 := by
    simpa [prefixWord, tailWord_652332, baseEnd_652332] using wordTrace_append hprefix tailTrace_652332
  have hstable : (prefixWord ++ tailWord_652332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652332).length < 2 ^ (prefixWord ++ tailWord_652332).sum := by decide
  have hdescent : baseEnd_652332 < baseStart_652332 := by decide
  rcases family_descends (prefixWord ++ tailWord_652332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652349 : List Nat := [1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_652349 : Nat := 118140960795 + 652349 * 2 ^ 59
def prefixEnd_652349 : Nat := 4983230072969 + 3 ^ 40 * 652349 * 2
def baseEnd_652349 : Nat := 99249953031103234144417

theorem tailTrace_652349 : CollatzResearch.WordTrace tailWord_652349 prefixEnd_652349 99249953031103234144417 := by
  unfold tailWord_652349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793122713658460184320101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15862081809105640122880067 23793122713658460184320101)
  ·
    refine ⟨4461210508810961284560019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23793122713658460184320101 4461210508810961284560019)
    ·
      refine ⟨6691815763216441926840029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4461210508810961284560019 6691815763216441926840029)
      ·
        refine ⟨2509430911206165722565011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6691815763216441926840029 2509430911206165722565011)
        ·
          refine ⟨3764146366809248583847517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509430911206165722565011 3764146366809248583847517)
          ·
            refine ⟨1411554887553468218942819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3764146366809248583847517 1411554887553468218942819)
            ·
              refine ⟨2117332331330202328414229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411554887553468218942819 2117332331330202328414229)
              ·
                refine ⟨99249953031103234144417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2117332331330202328414229 99249953031103234144417)
                ·
                  rfl

theorem cell20_652349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_652349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652349 prefixEnd_652349 := by exact prefixLift 652349
  have htrace : WordTrace (prefixWord ++ tailWord_652349) baseStart_652349 baseEnd_652349 := by
    simpa [prefixWord, tailWord_652349, baseEnd_652349] using wordTrace_append hprefix tailTrace_652349
  have hstable : (prefixWord ++ tailWord_652349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652349).length < 2 ^ (prefixWord ++ tailWord_652349).sum := by decide
  have hdescent : baseEnd_652349 < baseStart_652349 := by decide
  rcases family_descends (prefixWord ++ tailWord_652349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652359 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 2]
def baseStart_652359 : Nat := 118140960795 + 652359 * 2 ^ 59
def prefixEnd_652359 : Nat := 4983230072969 + 3 ^ 40 * 652359 * 2
def baseEnd_652359 : Nat := 297754423365794112099877

theorem tailTrace_652359 : CollatzResearch.WordTrace tailWord_652359 prefixEnd_652359 297754423365794112099877 := by
  unfold tailWord_652359
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793487443622231892184131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15862324962414821261456087 23793487443622231892184131)
  ·
    refine ⟨35690231165433347838276197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23793487443622231892184131 35690231165433347838276197)
    ·
      refine ⟨6691918343518752719676787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35690231165433347838276197 6691918343518752719676787)
      ·
        refine ⟨10037877515278129079515181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691918343518752719676787 10037877515278129079515181)
        ·
          refine ⟨3764204068229298404818193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10037877515278129079515181 3764204068229298404818193)
          ·
            refine ⟨2823153051171973803613645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764204068229298404818193 2823153051171973803613645)
            ·
              refine ⟨1058682394189490176355117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2823153051171973803613645 1058682394189490176355117)
              ·
                refine ⟨397005897821058816133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058682394189490176355117 397005897821058816133169)
                ·
                  refine ⟨297754423365794112099877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397005897821058816133169 297754423365794112099877)
                  ·
                    rfl

theorem cell20_652359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2].length) (baseStart_652359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652359 prefixEnd_652359 := by exact prefixLift 652359
  have htrace : WordTrace (prefixWord ++ tailWord_652359) baseStart_652359 baseEnd_652359 := by
    simpa [prefixWord, tailWord_652359, baseEnd_652359] using wordTrace_append hprefix tailTrace_652359
  have hstable : (prefixWord ++ tailWord_652359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652359).length < 2 ^ (prefixWord ++ tailWord_652359).sum := by decide
  have hdescent : baseEnd_652359 < baseStart_652359 := by decide
  rcases family_descends (prefixWord ++ tailWord_652359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652408 : List Nat := [2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_652408 : Nat := 118140960795 + 652408 * 2 ^ 59
def prefixEnd_652408 : Nat := 4983230072969 + 3 ^ 40 * 652408 * 2
def baseEnd_652408 : Nat := 99258929433655906488781

theorem tailTrace_652408 : CollatzResearch.WordTrace tailWord_652408 prefixEnd_652408 99258929433655906488781 := by
  unfold tailWord_652408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897637310222356630358939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15863516413629808840478585 11897637310222356630358939)
  ·
    refine ⟨17846455965333534945538409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11897637310222356630358939 17846455965333534945538409)
    ·
      refine ⟨13384841974000151209153807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17846455965333534945538409 13384841974000151209153807)
      ·
        refine ⟨20077262961000226813730711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384841974000151209153807 20077262961000226813730711)
        ·
          refine ⟨30115894441500340220596067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20077262961000226813730711 30115894441500340220596067)
          ·
            refine ⟨45173841662250510330894101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30115894441500340220596067 45173841662250510330894101)
            ·
              refine ⟨2117523827917992671760661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45173841662250510330894101 2117523827917992671760661)
              ·
                refine ⟨99258929433655906488781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2117523827917992671760661 99258929433655906488781)
                ·
                  rfl

theorem cell20_652408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_652408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652408 prefixEnd_652408 := by exact prefixLift 652408
  have htrace : WordTrace (prefixWord ++ tailWord_652408) baseStart_652408 baseEnd_652408 := by
    simpa [prefixWord, tailWord_652408, baseEnd_652408] using wordTrace_append hprefix tailTrace_652408
  have hstable : (prefixWord ++ tailWord_652408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652408).length < 2 ^ (prefixWord ++ tailWord_652408).sum := by decide
  have hdescent : baseEnd_652408 < baseStart_652408 := by decide
  rcases family_descends (prefixWord ++ tailWord_652408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652435 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 2]
def baseStart_652435 : Nat := 118140960795 + 652435 * 2 ^ 59
def prefixEnd_652435 : Nat := 4983230072969 + 3 ^ 40 * 652435 * 2
def baseEnd_652435 : Nat := 297789111836675625566233

theorem tailTrace_652435 : CollatzResearch.WordTrace tailWord_652435 prefixEnd_652435 297789111836675625566233 := by
  unfold tailWord_652435
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796259391346896871950759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15864172927564597914633839 23796259391346896871950759)
  ·
    refine ⟨35694389087020345307926139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23796259391346896871950759 35694389087020345307926139)
    ·
      refine ⟨53541583630530517961889209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35694389087020345307926139 53541583630530517961889209)
      ·
        refine ⟨40156187722897888471416907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53541583630530517961889209 40156187722897888471416907)
        ·
          refine ⟨60234281584346832707125361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40156187722897888471416907 60234281584346832707125361)
          ·
            refine ⟨45175711188260124530344021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60234281584346832707125361 45175711188260124530344021)
            ·
              refine ⟨529402865487423334339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45175711188260124530344021 529402865487423334339969)
              ·
                refine ⟨397052149115567500754977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529402865487423334339969 397052149115567500754977)
                ·
                  refine ⟨297789111836675625566233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397052149115567500754977 297789111836675625566233)
                  ·
                    rfl

theorem cell20_652435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2].length) (baseStart_652435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652435 prefixEnd_652435 := by exact prefixLift 652435
  have htrace : WordTrace (prefixWord ++ tailWord_652435) baseStart_652435 baseEnd_652435 := by
    simpa [prefixWord, tailWord_652435, baseEnd_652435] using wordTrace_append hprefix tailTrace_652435
  have hstable : (prefixWord ++ tailWord_652435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652435).length < 2 ^ (prefixWord ++ tailWord_652435).sum := by decide
  have hdescent : baseEnd_652435 < baseStart_652435 := by decide
  rcases family_descends (prefixWord ++ tailWord_652435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652442 : List Nat := [3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_652442 : Nat := 118140960795 + 652442 * 2 ^ 59
def prefixEnd_652442 : Nat := 4983230072969 + 3 ^ 40 * 652442 * 2
def baseEnd_652442 : Nat := 99264102275804904110957

theorem tailTrace_652442 : CollatzResearch.WordTrace tailWord_652442 prefixEnd_652442 99264102275804904110957 := by
  unfold tailWord_652442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949128675580384266863895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15864343134881024711637053 5949128675580384266863895)
  ·
    refine ⟨8923693013370576400295843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949128675580384266863895 8923693013370576400295843)
    ·
      refine ⟨13385539520055864600443765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923693013370576400295843 13385539520055864600443765)
      ·
        refine ⟨1254894330005237306291603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13385539520055864600443765 1254894330005237306291603)
        ·
          refine ⟨1882341495007855959437405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254894330005237306291603 1882341495007855959437405)
          ·
            refine ⟨705878060627945984789027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1882341495007855959437405 705878060627945984789027)
            ·
              refine ⟨1058817090941918977183541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705878060627945984789027 1058817090941918977183541)
              ·
                refine ⟨99264102275804904110957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1058817090941918977183541 99264102275804904110957)
                ·
                  rfl

theorem cell20_652442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_652442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652442 prefixEnd_652442 := by exact prefixLift 652442
  have htrace : WordTrace (prefixWord ++ tailWord_652442) baseStart_652442 baseEnd_652442 := by
    simpa [prefixWord, tailWord_652442, baseEnd_652442] using wordTrace_append hprefix tailTrace_652442
  have hstable : (prefixWord ++ tailWord_652442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652442).length < 2 ^ (prefixWord ++ tailWord_652442).sum := by decide
  have hdescent : baseEnd_652442 < baseStart_652442 := by decide
  rcases family_descends (prefixWord ++ tailWord_652442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652473 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 2]
def baseStart_652473 : Nat := 118140960795 + 652473 * 2 ^ 59
def prefixEnd_652473 : Nat := 4983230072969 + 3 ^ 40 * 652473 * 2
def baseEnd_652473 : Nat := 297806456072116382299411

theorem tailTrace_652473 : CollatzResearch.WordTrace tailWord_652473 prefixEnd_652473 297806456072116382299411 := by
  unfold tailWord_652473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797645365209229361834073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15865096910139486241222715 23797645365209229361834073)
  ·
    refine ⟨17848234023906922021375555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23797645365209229361834073 17848234023906922021375555)
    ·
      refine ⟨26772351035860383032063333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17848234023906922021375555 26772351035860383032063333)
      ·
        refine ⟨5019815819223821818511875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26772351035860383032063333 5019815819223821818511875)
        ·
          refine ⟨7529723728835732727767813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019815819223821818511875 7529723728835732727767813)
          ·
            refine ⟨1411823199156699886456465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7529723728835732727767813 1411823199156699886456465)
            ·
              refine ⟨1058867399367524914842349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411823199156699886456465 1058867399367524914842349)
              ·
                refine ⟨397075274762821843065881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058867399367524914842349 397075274762821843065881)
                ·
                  refine ⟨297806456072116382299411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397075274762821843065881 297806456072116382299411)
                  ·
                    rfl

theorem cell20_652473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_652473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652473 prefixEnd_652473 := by exact prefixLift 652473
  have htrace : WordTrace (prefixWord ++ tailWord_652473) baseStart_652473 baseEnd_652473 := by
    simpa [prefixWord, tailWord_652473, baseEnd_652473] using wordTrace_append hprefix tailTrace_652473
  have hstable : (prefixWord ++ tailWord_652473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652473).length < 2 ^ (prefixWord ++ tailWord_652473).sum := by decide
  have hdescent : baseEnd_652473 < baseStart_652473 := by decide
  rcases family_descends (prefixWord ++ tailWord_652473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652504 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_652504 : Nat := 118140960795 + 652504 * 2 ^ 59
def prefixEnd_652504 : Nat := 4983230072969 + 3 ^ 40 * 652504 * 2
def baseEnd_652504 : Nat := 297820605316818052265951

theorem tailTrace_652504 : CollatzResearch.WordTrace tailWord_652504 prefixEnd_652504 297820605316818052265951 := by
  unfold tailWord_652504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899388014048460828106283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15865850685397947770808377 11899388014048460828106283)
  ·
    refine ⟨17849082021072691242159425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899388014048460828106283 17849082021072691242159425)
    ·
      refine ⟨13386811515804518431619569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17849082021072691242159425 13386811515804518431619569)
      ·
        refine ⟨10040108636853388823714677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13386811515804518431619569 10040108636853388823714677)
        ·
          refine ⟨941260184705005202223251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10040108636853388823714677 941260184705005202223251)
          ·
            refine ⟨1411890277057507803334877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941260184705005202223251 1411890277057507803334877)
            ·
              refine ⟨529458853896565426250579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411890277057507803334877 529458853896565426250579)
              ·
                refine ⟨794188280844848139375869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529458853896565426250579 794188280844848139375869)
                ·
                  refine ⟨297820605316818052265951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794188280844848139375869 297820605316818052265951)
                  ·
                    rfl

theorem cell20_652504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_652504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652504 prefixEnd_652504 := by exact prefixLift 652504
  have htrace : WordTrace (prefixWord ++ tailWord_652504) baseStart_652504 baseEnd_652504 := by
    simpa [prefixWord, tailWord_652504, baseEnd_652504] using wordTrace_append hprefix tailTrace_652504
  have hstable : (prefixWord ++ tailWord_652504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652504).length < 2 ^ (prefixWord ++ tailWord_652504).sum := by decide
  have hdescent : baseEnd_652504 < baseStart_652504 := by decide
  rcases family_descends (prefixWord ++ tailWord_652504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652549 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 2]
def baseStart_652549 : Nat := 118140960795 + 652549 * 2 ^ 59
def prefixEnd_652549 : Nat := 4983230072969 + 3 ^ 40 * 652549 * 2
def baseEnd_652549 : Nat := 297841144542997895765767

theorem tailTrace_652549 : CollatzResearch.WordTrace tailWord_652549 prefixEnd_652549 297841144542997895765767 := by
  unfold tailWord_652549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800417312933894341600701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15866944875289262894400467 23800417312933894341600701)
  ·
    refine ⟨8925156492350210378100263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23800417312933894341600701 8925156492350210378100263)
    ·
      refine ⟨13387734738525315567150395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8925156492350210378100263 13387734738525315567150395)
      ·
        refine ⟨20081602107787973350725593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13387734738525315567150395 20081602107787973350725593)
        ·
          refine ⟨15061201580840980013044195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20081602107787973350725593 15061201580840980013044195)
          ·
            refine ⟨22591802371261470019566293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15061201580840980013044195 22591802371261470019566293)
            ·
              refine ⟨529495368076440703583585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22591802371261470019566293 529495368076440703583585)
              ·
                refine ⟨397121526057330527687689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529495368076440703583585 397121526057330527687689)
                ·
                  refine ⟨297841144542997895765767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397121526057330527687689 297841144542997895765767)
                  ·
                    rfl

theorem cell20_652549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_652549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652549 prefixEnd_652549 := by exact prefixLift 652549
  have htrace : WordTrace (prefixWord ++ tailWord_652549) baseStart_652549 baseEnd_652549 := by
    simpa [prefixWord, tailWord_652549, baseEnd_652549] using wordTrace_append hprefix tailTrace_652549
  have hstable : (prefixWord ++ tailWord_652549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652549).length < 2 ^ (prefixWord ++ tailWord_652549).sum := by decide
  have hdescent : baseEnd_652549 < baseStart_652549 := by decide
  rcases family_descends (prefixWord ++ tailWord_652549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652604 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_652604 : Nat := 118140960795 + 652604 * 2 ^ 59
def prefixEnd_652604 : Nat := 4983230072969 + 3 ^ 40 * 652604 * 2
def baseEnd_652604 : Nat := 297866248041662148932209

theorem tailTrace_652604 : CollatzResearch.WordTrace tailWord_652604 prefixEnd_652604 297866248041662148932209 := by
  unfold tailWord_652604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901211663867319367426433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15868282218489759156568577 11901211663867319367426433)
  ·
    refine ⟨8925908747900489525569825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11901211663867319367426433 8925908747900489525569825)
    ·
      refine ⟨6694431560925367144177369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8925908747900489525569825 6694431560925367144177369)
      ·
        refine ⟨5020823670694025358133027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6694431560925367144177369 5020823670694025358133027)
        ·
          refine ⟨7531235506041038037199541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020823670694025358133027 7531235506041038037199541)
          ·
            refine ⟨706053328691347315987457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7531235506041038037199541 706053328691347315987457)
            ·
              refine ⟨529539996518510486990593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706053328691347315987457 529539996518510486990593)
              ·
                refine ⟨397154997388882865242945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529539996518510486990593 397154997388882865242945)
                ·
                  refine ⟨297866248041662148932209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397154997388882865242945 297866248041662148932209)
                  ·
                    rfl

theorem cell20_652604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_652604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652604 prefixEnd_652604 := by exact prefixLift 652604
  have htrace : WordTrace (prefixWord ++ tailWord_652604) baseStart_652604 baseEnd_652604 := by
    simpa [prefixWord, tailWord_652604, baseEnd_652604] using wordTrace_append hprefix tailTrace_652604
  have hstable : (prefixWord ++ tailWord_652604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652604).length < 2 ^ (prefixWord ++ tailWord_652604).sum := by decide
  have hdescent : baseEnd_652604 < baseStart_652604 := by decide
  rcases family_descends (prefixWord ++ tailWord_652604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652608 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_652608 : Nat := 118140960795 + 652608 * 2 ^ 59
def prefixEnd_652608 : Nat := 4983230072969 + 3 ^ 40 * 652608 * 2
def baseEnd_652608 : Nat := 297868073750655912798859

theorem tailTrace_652608 : CollatzResearch.WordTrace tailWord_652608 prefixEnd_652608 297868073750655912798859 := by
  unfold tailWord_652608
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901284609860073708999239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15868379479813431611998985 11901284609860073708999239)
  ·
    refine ⟨17851926914790110563498859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11901284609860073708999239 17851926914790110563498859)
    ·
      refine ⟨26777890372185165845248289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17851926914790110563498859 26777890372185165845248289)
      ·
        refine ⟨20083417779138874383936217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26777890372185165845248289 20083417779138874383936217)
        ·
          refine ⟨15062563334354155787952163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20083417779138874383936217 15062563334354155787952163)
          ·
            refine ⟨22593845001531233681928245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062563334354155787952163 22593845001531233681928245)
            ·
              refine ⟨2118172968893553157680773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22593845001531233681928245 2118172968893553157680773)
              ·
                refine ⟨397157431667541217065145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2118172968893553157680773 397157431667541217065145)
                ·
                  refine ⟨297868073750655912798859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397157431667541217065145 297868073750655912798859)
                  ·
                    rfl

theorem cell20_652608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_652608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652608 prefixEnd_652608 := by exact prefixLift 652608
  have htrace : WordTrace (prefixWord ++ tailWord_652608) baseStart_652608 baseEnd_652608 := by
    simpa [prefixWord, tailWord_652608, baseEnd_652608] using wordTrace_append hprefix tailTrace_652608
  have hstable : (prefixWord ++ tailWord_652608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652608).length < 2 ^ (prefixWord ++ tailWord_652608).sum := by decide
  have hdescent : baseEnd_652608 < baseStart_652608 := by decide
  rcases family_descends (prefixWord ++ tailWord_652608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652615 : List Nat := [1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_652615 : Nat := 118140960795 + 652615 * 2 ^ 59
def prefixEnd_652615 : Nat := 4983230072969 + 3 ^ 40 * 652615 * 2
def baseEnd_652615 : Nat := 99290422913798333188499

theorem tailTrace_652615 : CollatzResearch.WordTrace tailWord_652615 prefixEnd_652615 99290422913798333188499 := by
  unfold tailWord_652615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23802824530694787613503299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15868549687129858409002199 23802824530694787613503299)
  ·
    refine ⟨35704236796042181420254949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23802824530694787613503299 35704236796042181420254949)
    ·
      refine ⟨6694544399257909016297803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35704236796042181420254949 6694544399257909016297803)
      ·
        refine ⟨10041816598886863524446705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6694544399257909016297803 10041816598886863524446705)
        ·
          refine ⟨7531362449165147643335029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10041816598886863524446705 7531362449165147643335029)
          ·
            refine ⟨706065229609232591562659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7531362449165147643335029 706065229609232591562659)
            ·
              refine ⟨1059097844413848887343989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706065229609232591562659 1059097844413848887343989)
              ·
                refine ⟨99290422913798333188499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059097844413848887343989 99290422913798333188499)
                ·
                  rfl

theorem cell20_652615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_652615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652615 prefixEnd_652615 := by exact prefixLift 652615
  have htrace : WordTrace (prefixWord ++ tailWord_652615) baseStart_652615 baseEnd_652615 := by
    simpa [prefixWord, tailWord_652615, baseEnd_652615] using wordTrace_append hprefix tailTrace_652615
  have hstable : (prefixWord ++ tailWord_652615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652615).length < 2 ^ (prefixWord ++ tailWord_652615).sum := by decide
  have hdescent : baseEnd_652615 < baseStart_652615 := by decide
  rcases family_descends (prefixWord ++ tailWord_652615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652622 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_652622 : Nat := 118140960795 + 652622 * 2 ^ 59
def prefixEnd_652622 : Nat := 4983230072969 + 3 ^ 40 * 652622 * 2
def baseEnd_652622 : Nat := 297874463732134086332135

theorem tailTrace_652622 : CollatzResearch.WordTrace tailWord_652622 prefixEnd_652622 297874463732134086332135 := by
  unfold tailWord_652622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975384980208678476126015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15868719894446285206005413 2975384980208678476126015)
  ·
    refine ⟨4463077470313017714189023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975384980208678476126015 4463077470313017714189023)
    ·
      refine ⟨6694616205469526571283535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463077470313017714189023 6694616205469526571283535)
      ·
        refine ⟨10041924308204289856925303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6694616205469526571283535 10041924308204289856925303)
        ·
          refine ⟨15062886462306434785387955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10041924308204289856925303 15062886462306434785387955)
          ·
            refine ⟨22594329693459652178081933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062886462306434785387955 22594329693459652178081933)
            ·
              refine ⟨8472873635047369566780725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22594329693459652178081933 8472873635047369566780725)
              ·
                refine ⟨794331903285690896885693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8472873635047369566780725 794331903285690896885693)
                ·
                  refine ⟨297874463732134086332135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794331903285690896885693 297874463732134086332135)
                  ·
                    rfl

theorem cell20_652622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_652622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652622 prefixEnd_652622 := by exact prefixLift 652622
  have htrace : WordTrace (prefixWord ++ tailWord_652622) baseStart_652622 baseEnd_652622 := by
    simpa [prefixWord, tailWord_652622, baseEnd_652622] using wordTrace_append hprefix tailTrace_652622
  have hstable : (prefixWord ++ tailWord_652622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652622).length < 2 ^ (prefixWord ++ tailWord_652622).sum := by decide
  have hdescent : baseEnd_652622 < baseStart_652622 := by decide
  rcases family_descends (prefixWord ++ tailWord_652622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652629 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_652629 : Nat := 118140960795 + 652629 * 2 ^ 59
def prefixEnd_652629 : Nat := 4983230072969 + 3 ^ 40 * 652629 * 2
def baseEnd_652629 : Nat := 297877658722873173098773

theorem tailTrace_652629 : CollatzResearch.WordTrace tailWord_652629 prefixEnd_652629 297877658722873173098773 := by
  unfold tailWord_652629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803335152644068004512941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15868890101762712003008627 23803335152644068004512941)
  ·
    refine ⟨8926250682241525501692353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23803335152644068004512941 8926250682241525501692353)
    ·
      refine ⟨6694688011681144126269265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8926250682241525501692353 6694688011681144126269265)
      ·
        refine ⟨5021016008760858094701949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6694688011681144126269265 5021016008760858094701949)
        ·
          refine ⟨1882881003285321785513231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5021016008760858094701949 1882881003285321785513231)
          ·
            refine ⟨2824321504927982678269847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882881003285321785513231 2824321504927982678269847)
            ·
              refine ⟨4236482257391974017404771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824321504927982678269847 4236482257391974017404771)
              ·
                refine ⟨6354723386087961026107157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4236482257391974017404771 6354723386087961026107157)
                ·
                  refine ⟨297877658722873173098773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6354723386087961026107157 297877658722873173098773)
                  ·
                    rfl

theorem cell20_652629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_652629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652629 prefixEnd_652629 := by exact prefixLift 652629
  have htrace : WordTrace (prefixWord ++ tailWord_652629) baseStart_652629 baseEnd_652629 := by
    simpa [prefixWord, tailWord_652629, baseEnd_652629] using wordTrace_append hprefix tailTrace_652629
  have hstable : (prefixWord ++ tailWord_652629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652629).length < 2 ^ (prefixWord ++ tailWord_652629).sum := by decide
  have hdescent : baseEnd_652629 < baseStart_652629 := by decide
  rcases family_descends (prefixWord ++ tailWord_652629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652667 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_652667 : Nat := 118140960795 + 652667 * 2 ^ 59
def prefixEnd_652667 : Nat := 4983230072969 + 3 ^ 40 * 652667 * 2
def baseEnd_652667 : Nat := 297895002958313929831951

theorem tailTrace_652667 : CollatzResearch.WordTrace tailWord_652667 prefixEnd_652667 297895002958313929831951 := by
  unfold tailWord_652667
  simp only [CollatzResearch.WordTrace]
  refine ⟨23804721126506400494396255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15869814084337600329597503 23804721126506400494396255)
  ·
    refine ⟨35707081689759600741594383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23804721126506400494396255 35707081689759600741594383)
    ·
      refine ⟨53560622534639401112391575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35707081689759600741594383 53560622534639401112391575)
      ·
        refine ⟨80340933801959101668587363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53560622534639401112391575 80340933801959101668587363)
        ·
          refine ⟨120511400702938652502881045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80340933801959101668587363 120511400702938652502881045)
          ·
            refine ⟨5648971907950249336072549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120511400702938652502881045 5648971907950249336072549)
            ·
              refine ⟨1059182232740671750513603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5648971907950249336072549 1059182232740671750513603)
              ·
                refine ⟨1588773349111007625770405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059182232740671750513603 1588773349111007625770405)
                ·
                  refine ⟨297895002958313929831951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1588773349111007625770405 297895002958313929831951)
                  ·
                    rfl

theorem cell20_652667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_652667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652667 prefixEnd_652667 := by exact prefixLift 652667
  have htrace : WordTrace (prefixWord ++ tailWord_652667) baseStart_652667 baseEnd_652667 := by
    simpa [prefixWord, tailWord_652667, baseEnd_652667] using wordTrace_append hprefix tailTrace_652667
  have hstable : (prefixWord ++ tailWord_652667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652667).length < 2 ^ (prefixWord ++ tailWord_652667).sum := by decide
  have hdescent : baseEnd_652667 < baseStart_652667 := by decide
  rcases family_descends (prefixWord ++ tailWord_652667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652701 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 2]
def baseStart_652701 : Nat := 118140960795 + 652701 * 2 ^ 59
def prefixEnd_652701 : Nat := 4983230072969 + 3 ^ 40 * 652701 * 2
def baseEnd_652701 : Nat := 297910521484760922698479

theorem tailTrace_652701 : CollatzResearch.WordTrace tailWord_652701 prefixEnd_652701 297910521484760922698479 := by
  unfold tailWord_652701
  simp only [CollatzResearch.WordTrace]
  refine ⟨23805961208383224301133957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15870640805588816200755971 23805961208383224301133957)
  ·
    refine ⟨4463617726571854556462617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23805961208383224301133957 4463617726571854556462617)
    ·
      refine ⟨3347713294928890917346963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4463617726571854556462617 3347713294928890917346963)
      ·
        refine ⟨5021569942393336376020445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347713294928890917346963 5021569942393336376020445)
        ·
          refine ⟨1883088728397501141007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5021569942393336376020445 1883088728397501141007667)
          ·
            refine ⟨2824633092596251711511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883088728397501141007667 2824633092596251711511501)
            ·
              refine ⟨1059237409723594391816813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2824633092596251711511501 1059237409723594391816813)
              ·
                refine ⟨397214028646347896931305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059237409723594391816813 397214028646347896931305)
                ·
                  refine ⟨297910521484760922698479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397214028646347896931305 297910521484760922698479)
                  ·
                    rfl

theorem cell20_652701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_652701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652701 prefixEnd_652701 := by exact prefixLift 652701
  have htrace : WordTrace (prefixWord ++ tailWord_652701) baseStart_652701 baseEnd_652701 := by
    simpa [prefixWord, tailWord_652701, baseEnd_652701] using wordTrace_append hprefix tailTrace_652701
  have hstable : (prefixWord ++ tailWord_652701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652701).length < 2 ^ (prefixWord ++ tailWord_652701).sum := by decide
  have hdescent : baseEnd_652701 < baseStart_652701 := by decide
  rcases family_descends (prefixWord ++ tailWord_652701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652729 : List Nat := [1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_652729 : Nat := 118140960795 + 652729 * 2 ^ 59
def prefixEnd_652729 : Nat := 4983230072969 + 3 ^ 40 * 652729 * 2
def baseEnd_652729 : Nat := 99307767149239089921677

theorem tailTrace_652729 : CollatzResearch.WordTrace tailWord_652729 prefixEnd_652729 99307767149239089921677 := by
  unfold tailWord_652729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23806982452281785083153241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15871321634854523388768827 23806982452281785083153241)
  ·
    refine ⟨17855236839211338812364931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23806982452281785083153241 17855236839211338812364931)
    ·
      refine ⟨26782855258817008218547397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17855236839211338812364931 26782855258817008218547397)
      ·
        refine ⟨5021785361028189040977637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26782855258817008218547397 5021785361028189040977637)
        ·
          refine ⟨941584755192785445183307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5021785361028189040977637 941584755192785445183307)
          ·
            refine ⟨1412377132789178167774961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941584755192785445183307 1412377132789178167774961)
            ·
              refine ⟨1059282849591883625831221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412377132789178167774961 1059282849591883625831221)
              ·
                refine ⟨99307767149239089921677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059282849591883625831221 99307767149239089921677)
                ·
                  rfl

theorem cell20_652729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_652729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652729 prefixEnd_652729 := by exact prefixLift 652729
  have htrace : WordTrace (prefixWord ++ tailWord_652729) baseStart_652729 baseEnd_652729 := by
    simpa [prefixWord, tailWord_652729, baseEnd_652729] using wordTrace_append hprefix tailTrace_652729
  have hstable : (prefixWord ++ tailWord_652729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652729).length < 2 ^ (prefixWord ++ tailWord_652729).sum := by decide
  have hdescent : baseEnd_652729 < baseStart_652729 := by decide
  rcases family_descends (prefixWord ++ tailWord_652729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652750 : List Nat := [4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_652750 : Nat := 118140960795 + 652750 * 2 ^ 59
def prefixEnd_652750 : Nat := 4983230072969 + 3 ^ 40 * 652750 * 2
def baseEnd_652750 : Nat := 99310962139978176688315

theorem tailTrace_652750 : CollatzResearch.WordTrace tailWord_652750 prefixEnd_652750 99310962139978176688315 := by
  unfold tailWord_652750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975968548150713208708463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15871832256803803779778469 2975968548150713208708463)
  ·
    refine ⟨4463952822226069813062695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975968548150713208708463 4463952822226069813062695)
    ·
      refine ⟨6695929233339104719594043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463952822226069813062695 6695929233339104719594043)
      ·
        refine ⟨10043893850008657079391065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695929233339104719594043 10043893850008657079391065)
        ·
          refine ⟨7532920387506492809543299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10043893850008657079391065 7532920387506492809543299)
          ·
            refine ⟨11299380581259739214314949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7532920387506492809543299 11299380581259739214314949)
            ·
              refine ⟨2118633858986201102684053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11299380581259739214314949 2118633858986201102684053)
              ·
                refine ⟨99310962139978176688315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2118633858986201102684053 99310962139978176688315)
                ·
                  rfl

theorem cell20_652750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_652750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652750 prefixEnd_652750 := by exact prefixLift 652750
  have htrace : WordTrace (prefixWord ++ tailWord_652750) baseStart_652750 baseEnd_652750 := by
    simpa [prefixWord, tailWord_652750, baseEnd_652750] using wordTrace_append hprefix tailTrace_652750
  have hstable : (prefixWord ++ tailWord_652750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652750).length < 2 ^ (prefixWord ++ tailWord_652750).sum := by decide
  have hdescent : baseEnd_652750 < baseStart_652750 := by decide
  rcases family_descends (prefixWord ++ tailWord_652750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652846 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_652846 : Nat := 118140960795 + 652846 * 2 ^ 59
def prefixEnd_652846 : Nat := 4983230072969 + 3 ^ 40 * 652846 * 2
def baseEnd_652846 : Nat := 297976703435784862864553

theorem tailTrace_652846 : CollatzResearch.WordTrace tailWord_652846 prefixEnd_652846 297976703435784862864553 := by
  unfold tailWord_652846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976406224107239258145299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15874166528571942710108261 2976406224107239258145299)
  ·
    refine ⟨4464609336160858887217949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976406224107239258145299 4464609336160858887217949)
    ·
      refine ⟨1674228501060322082706731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4464609336160858887217949 1674228501060322082706731)
      ·
        refine ⟨2511342751590483124060097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674228501060322082706731 2511342751590483124060097)
        ·
          refine ⟨1883507063692862343045073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511342751590483124060097 1883507063692862343045073)
          ·
            refine ⟨1412630297769646757283805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883507063692862343045073 1412630297769646757283805)
            ·
              refine ⟨529736361663617533981427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1412630297769646757283805 529736361663617533981427)
              ·
                refine ⟨794604542495426300972141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529736361663617533981427 794604542495426300972141)
                ·
                  refine ⟨297976703435784862864553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794604542495426300972141 297976703435784862864553)
                  ·
                    rfl

theorem cell20_652846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_652846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652846 prefixEnd_652846 := by exact prefixLift 652846
  have htrace : WordTrace (prefixWord ++ tailWord_652846) baseStart_652846 baseEnd_652846 := by
    simpa [prefixWord, tailWord_652846, baseEnd_652846] using wordTrace_append hprefix tailTrace_652846
  have hstable : (prefixWord ++ tailWord_652846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652846).length < 2 ^ (prefixWord ++ tailWord_652846).sum := by decide
  have hdescent : baseEnd_652846 < baseStart_652846 := by decide
  rcases family_descends (prefixWord ++ tailWord_652846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652857 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_652857 : Nat := 118140960795 + 652857 * 2 ^ 59
def prefixEnd_652857 : Nat := 4983230072969 + 3 ^ 40 * 652857 * 2
def baseEnd_652857 : Nat := 297981724135517713497841

theorem tailTrace_652857 : CollatzResearch.WordTrace tailWord_652857 prefixEnd_652857 297981724135517713497841 := by
  unfold tailWord_652857
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811650995818062943812825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15874433997212041962541883 23811650995818062943812825)
  ·
    refine ⟨17858738246863547207859619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23811650995818062943812825 17858738246863547207859619)
    ·
      refine ⟨26788107370295320811789429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17858738246863547207859619 26788107370295320811789429)
      ·
        refine ⟨2511385065965186326105259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26788107370295320811789429 2511385065965186326105259)
        ·
          refine ⟨3767077598947779489157889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511385065965186326105259 3767077598947779489157889)
          ·
            refine ⟨2825308199210834616868417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767077598947779489157889 2825308199210834616868417)
            ·
              refine ⟨2118981149408125962651313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825308199210834616868417 2118981149408125962651313)
              ·
                refine ⟨1589235862056094471988485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118981149408125962651313 1589235862056094471988485)
                ·
                  refine ⟨297981724135517713497841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589235862056094471988485 297981724135517713497841)
                  ·
                    rfl

theorem cell20_652857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_652857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652857 prefixEnd_652857 := by exact prefixLift 652857
  have htrace : WordTrace (prefixWord ++ tailWord_652857) baseStart_652857 baseEnd_652857 := by
    simpa [prefixWord, tailWord_652857, baseEnd_652857] using wordTrace_append hprefix tailTrace_652857
  have hstable : (prefixWord ++ tailWord_652857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652857).length < 2 ^ (prefixWord ++ tailWord_652857).sum := by decide
  have hdescent : baseEnd_652857 < baseStart_652857 := by decide
  rcases family_descends (prefixWord ++ tailWord_652857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652860 : List Nat := [2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_652860 : Nat := 118140960795 + 652860 * 2 ^ 59
def prefixEnd_652860 : Nat := 4983230072969 + 3 ^ 40 * 652860 * 2
def baseEnd_652860 : Nat := 99327697805754345465943

theorem tailTrace_652860 : CollatzResearch.WordTrace tailWord_652860 prefixEnd_652860 99327697805754345465943 := by
  unfold tailWord_652860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905880207403597228086017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15874506943204796304114689 11905880207403597228086017)
  ·
    refine ⟨8929410155552697921064513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11905880207403597228086017 8929410155552697921064513)
    ·
      refine ⟨6697057616664523440798385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8929410155552697921064513 6697057616664523440798385)
      ·
        refine ⟨5022793212498392580598789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6697057616664523440798385 5022793212498392580598789)
        ·
          refine ⟨941773727343448608862273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5022793212498392580598789 941773727343448608862273)
          ·
            refine ⟨706330295507586456646705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941773727343448608862273 706330295507586456646705)
            ·
              refine ⟨529747721630689842485029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706330295507586456646705 529747721630689842485029)
              ·
                refine ⟨99327697805754345465943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529747721630689842485029 99327697805754345465943)
                ·
                  rfl

theorem cell20_652860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_652860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652860 prefixEnd_652860 := by exact prefixLift 652860
  have htrace : WordTrace (prefixWord ++ tailWord_652860) baseStart_652860 baseEnd_652860 := by
    simpa [prefixWord, tailWord_652860, baseEnd_652860] using wordTrace_append hprefix tailTrace_652860
  have hstable : (prefixWord ++ tailWord_652860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652860).length < 2 ^ (prefixWord ++ tailWord_652860).sum := by decide
  have hdescent : baseEnd_652860 < baseStart_652860 := by decide
  rcases family_descends (prefixWord ++ tailWord_652860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652923 : List Nat := [1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_652923 : Nat := 118140960795 + 652923 * 2 ^ 59
def prefixEnd_652923 : Nat := 4983230072969 + 3 ^ 40 * 652923 * 2
def baseEnd_652923 : Nat := 99337282777971605765857

theorem tailTrace_652923 : CollatzResearch.WordTrace tailWord_652923 prefixEnd_652923 99337282777971605765857 := by
  unfold tailWord_652923
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814058213578956215715423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15876038809052637477143615 23814058213578956215715423)
  ·
    refine ⟨35721087320368434323573135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23814058213578956215715423 35721087320368434323573135)
    ·
      refine ⟨53581630980552651485359703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35721087320368434323573135 53581630980552651485359703)
      ·
        refine ⟨80372446470828977228039555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53581630980552651485359703 80372446470828977228039555)
        ·
          refine ⟨120558669706243465842059333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80372446470828977228039555 120558669706243465842059333)
          ·
            refine ⟨22604750569920649845386125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120558669706243465842059333 22604750569920649845386125)
            ·
              refine ⟨8476781463720243692019797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22604750569920649845386125 8476781463720243692019797)
              ·
                refine ⟨99337282777971605765857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8476781463720243692019797 99337282777971605765857)
                ·
                  rfl

theorem cell20_652923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_652923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652923 prefixEnd_652923 := by exact prefixLift 652923
  have htrace : WordTrace (prefixWord ++ tailWord_652923) baseStart_652923 baseEnd_652923 := by
    simpa [prefixWord, tailWord_652923, baseEnd_652923] using wordTrace_append hprefix tailTrace_652923
  have hstable : (prefixWord ++ tailWord_652923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652923).length < 2 ^ (prefixWord ++ tailWord_652923).sum := by decide
  have hdescent : baseEnd_652923 < baseStart_652923 := by decide
  rcases family_descends (prefixWord ++ tailWord_652923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652964 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_652964 : Nat := 118140960795 + 652964 * 2 ^ 59
def prefixEnd_652964 : Nat := 4983230072969 + 3 ^ 40 * 652964 * 2
def baseEnd_652964 : Nat := 298030561851100896930737

theorem tailTrace_652964 : CollatzResearch.WordTrace tailWord_652964 prefixEnd_652964 298030561851100896930737 := by
  unfold tailWord_652964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907776803215210108978973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15877035737620280145305297 11907776803215210108978973)
  ·
    refine ⟨4465416301205703790867115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11907776803215210108978973 4465416301205703790867115)
    ·
      refine ⟨6698124451808555686300673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4465416301205703790867115 6698124451808555686300673)
      ·
        refine ⟨5023593338856416764725505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6698124451808555686300673 5023593338856416764725505)
        ·
          refine ⟨3767695004142312573544129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5023593338856416764725505 3767695004142312573544129)
          ·
            refine ⟨2825771253106734430158097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767695004142312573544129 2825771253106734430158097)
            ·
              refine ⟨2119328439830050822618573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825771253106734430158097 2119328439830050822618573)
              ·
                refine ⟨794748164936269058481965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2119328439830050822618573 794748164936269058481965)
                ·
                  refine ⟨298030561851100896930737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794748164936269058481965 298030561851100896930737)
                  ·
                    rfl

theorem cell20_652964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_652964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652964 prefixEnd_652964 := by exact prefixLift 652964
  have htrace : WordTrace (prefixWord ++ tailWord_652964) baseStart_652964 baseEnd_652964 := by
    simpa [prefixWord, tailWord_652964, baseEnd_652964] using wordTrace_append hprefix tailTrace_652964
  have hstable : (prefixWord ++ tailWord_652964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652964).length < 2 ^ (prefixWord ++ tailWord_652964).sum := by decide
  have hdescent : baseEnd_652964 < baseStart_652964 := by decide
  rcases family_descends (prefixWord ++ tailWord_652964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652988 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_652988 : Nat := 118140960795 + 652988 * 2 ^ 59
def prefixEnd_652988 : Nat := 4983230072969 + 3 ^ 40 * 652988 * 2
def baseEnd_652988 : Nat := 298041516105063480130639

theorem tailTrace_652988 : CollatzResearch.WordTrace tailWord_652988 prefixEnd_652988 298041516105063480130639 := by
  unfold tailWord_652988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908214479171736158415809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15877619305562314877887745 11908214479171736158415809)
  ·
    refine ⟨8931160859378802118811857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11908214479171736158415809 8931160859378802118811857)
    ·
      refine ⟨6698370644534101589108893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8931160859378802118811857 6698370644534101589108893)
      ·
        refine ⟨2511888991700288095915835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6698370644534101589108893 2511888991700288095915835)
        ·
          refine ⟨3767833487550432143873753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511888991700288095915835 3767833487550432143873753)
          ·
            refine ⟨2825875115662824107905315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767833487550432143873753 2825875115662824107905315)
            ·
              refine ⟨4238812673494236161857973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825875115662824107905315 4238812673494236161857973)
              ·
                refine ⟨397388688140084640174185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4238812673494236161857973 397388688140084640174185)
                ·
                  refine ⟨298041516105063480130639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397388688140084640174185 298041516105063480130639)
                  ·
                    rfl

theorem cell20_652988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_652988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652988 prefixEnd_652988 := by exact prefixLift 652988
  have htrace : WordTrace (prefixWord ++ tailWord_652988) baseStart_652988 baseEnd_652988 := by
    simpa [prefixWord, tailWord_652988, baseEnd_652988] using wordTrace_append hprefix tailTrace_652988
  have hstable : (prefixWord ++ tailWord_652988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652988).length < 2 ^ (prefixWord ++ tailWord_652988).sum := by decide
  have hdescent : baseEnd_652988 < baseStart_652988 := by decide
  rcases family_descends (prefixWord ++ tailWord_652988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652992 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_652992 : Nat := 118140960795 + 652992 * 2 ^ 59
def prefixEnd_652992 : Nat := 4983230072969 + 3 ^ 40 * 652992 * 2
def baseEnd_652992 : Nat := 298043341814057243997289

theorem tailTrace_652992 : CollatzResearch.WordTrace tailWord_652992 prefixEnd_652992 298043341814057243997289 := by
  unfold tailWord_652992
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908287425164490499988615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15877716566885987333318153 11908287425164490499988615)
  ·
    refine ⟨17862431137746735749982923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11908287425164490499988615 17862431137746735749982923)
    ·
      refine ⟨26793646706620103624974385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17862431137746735749982923 26793646706620103624974385)
      ·
        refine ⟨20095235029965077718730789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26793646706620103624974385 20095235029965077718730789)
        ·
          refine ⟨3767856568118452072262023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20095235029965077718730789 3767856568118452072262023)
          ·
            refine ⟨5651784852177678108393035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767856568118452072262023 5651784852177678108393035)
            ·
              refine ⟨8477677278266517162589553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651784852177678108393035 8477677278266517162589553)
              ·
                refine ⟨6358257958699887871942165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8477677278266517162589553 6358257958699887871942165)
                ·
                  refine ⟨298043341814057243997289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6358257958699887871942165 298043341814057243997289)
                  ·
                    rfl

theorem cell20_652992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_652992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652992 prefixEnd_652992 := by exact prefixLift 652992
  have htrace : WordTrace (prefixWord ++ tailWord_652992) baseStart_652992 baseEnd_652992 := by
    simpa [prefixWord, tailWord_652992, baseEnd_652992] using wordTrace_append hprefix tailTrace_652992
  have hstable : (prefixWord ++ tailWord_652992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652992).length < 2 ^ (prefixWord ++ tailWord_652992).sum := by decide
  have hdescent : baseEnd_652992 < baseStart_652992 := by decide
  rcases family_descends (prefixWord ++ tailWord_652992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652994 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_652994 : Nat := 118140960795 + 652994 * 2 ^ 59
def prefixEnd_652994 : Nat := 4983230072969 + 3 ^ 40 * 652994 * 2
def baseEnd_652994 : Nat := 298044254668554125930615

theorem tailTrace_652994 : CollatzResearch.WordTrace tailWord_652994 prefixEnd_652994 298044254668554125930615 := by
  unfold tailWord_652994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954161949080433835387509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15877765197547823561033357 5954161949080433835387509)
  ·
    refine ⟨558202682726290672067579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5954161949080433835387509 558202682726290672067579)
    ·
      refine ⟨837304024089436008101369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558202682726290672067579 837304024089436008101369)
      ·
        refine ⟨627978018067077006076027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837304024089436008101369 627978018067077006076027)
        ·
          refine ⟨941967027100615509114041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627978018067077006076027 941967027100615509114041)
          ·
            refine ⟨706475270325461631835531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941967027100615509114041 706475270325461631835531)
            ·
              refine ⟨1059712905488192447753297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706475270325461631835531 1059712905488192447753297)
              ·
                refine ⟨794784679116144335814973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059712905488192447753297 794784679116144335814973)
                ·
                  refine ⟨298044254668554125930615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794784679116144335814973 298044254668554125930615)
                  ·
                    rfl

theorem cell20_652994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_652994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652994 prefixEnd_652994 := by exact prefixLift 652994
  have htrace : WordTrace (prefixWord ++ tailWord_652994) baseStart_652994 baseEnd_652994 := by
    simpa [prefixWord, tailWord_652994, baseEnd_652994] using wordTrace_append hprefix tailTrace_652994
  have hstable : (prefixWord ++ tailWord_652994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652994).length < 2 ^ (prefixWord ++ tailWord_652994).sum := by decide
  have hdescent : baseEnd_652994 < baseStart_652994 := by decide
  rcases family_descends (prefixWord ++ tailWord_652994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652998 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_652998 : Nat := 118140960795 + 652998 * 2 ^ 59
def prefixEnd_652998 : Nat := 4983230072969 + 3 ^ 40 * 652998 * 2
def baseEnd_652998 : Nat := 298046080377547889797265

theorem tailTrace_652998 : CollatzResearch.WordTrace tailWord_652998 prefixEnd_652998 298046080377547889797265 := by
  unfold tailWord_652998
  simp only [CollatzResearch.WordTrace]
  refine ⟨744274802759601375771739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15877862458871496016463765 744274802759601375771739)
  ·
    refine ⟨1116412204139402063657609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744274802759601375771739 1116412204139402063657609)
    ·
      refine ⟨837309153104551547743207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116412204139402063657609 837309153104551547743207)
      ·
        refine ⟨1255963729656827321614811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837309153104551547743207 1255963729656827321614811)
        ·
          refine ⟨1883945594485240982422217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255963729656827321614811 1883945594485240982422217)
          ·
            refine ⟨1412959195863930736816663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883945594485240982422217 1412959195863930736816663)
            ·
              refine ⟨2119438793795896105224995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412959195863930736816663 2119438793795896105224995)
              ·
                refine ⟨3179158190693844157837493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119438793795896105224995 3179158190693844157837493)
                ·
                  refine ⟨298046080377547889797265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179158190693844157837493 298046080377547889797265)
                  ·
                    rfl

theorem cell20_652998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_652998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652998 prefixEnd_652998 := by exact prefixLift 652998
  have htrace : WordTrace (prefixWord ++ tailWord_652998) baseStart_652998 baseEnd_652998 := by
    simpa [prefixWord, tailWord_652998, baseEnd_652998] using wordTrace_append hprefix tailTrace_652998
  have hstable : (prefixWord ++ tailWord_652998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652998).length < 2 ^ (prefixWord ++ tailWord_652998).sum := by decide
  have hdescent : baseEnd_652998 < baseStart_652998 := by decide
  rcases family_descends (prefixWord ++ tailWord_652998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652999 : List Nat := [1, 1, 4, 1, 1, 1, 11]
def baseStart_652999 : Nat := 118140960795 + 652999 * 2 ^ 59
def prefixEnd_652999 : Nat := 4983230072969 + 3 ^ 40 * 652999 * 2
def baseEnd_652999 : Nat := 33116281867199592307103

theorem tailTrace_652999 : CollatzResearch.WordTrace tailWord_652999 prefixEnd_652999 33116281867199592307103 := by
  unfold tailWord_652999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816830161303621195482051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15877886774202414130321367 23816830161303621195482051)
  ·
    refine ⟨35725245241955431793223077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23816830161303621195482051 35725245241955431793223077)
    ·
      refine ⟨6698483482866643461229327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35725245241955431793223077 6698483482866643461229327)
      ·
        refine ⟨10047725224299965191843991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698483482866643461229327 10047725224299965191843991)
        ·
          refine ⟨15071587836449947787765987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047725224299965191843991 15071587836449947787765987)
          ·
            refine ⟨22607381754674921681648981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15071587836449947787765987 22607381754674921681648981)
            ·
              refine ⟨33116281867199592307103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22607381754674921681648981 33116281867199592307103)
              ·
                rfl

theorem cell20_652999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_652999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_652999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_652999 prefixEnd_652999 := by exact prefixLift 652999
  have htrace : WordTrace (prefixWord ++ tailWord_652999) baseStart_652999 baseEnd_652999 := by
    simpa [prefixWord, tailWord_652999, baseEnd_652999] using wordTrace_append hprefix tailTrace_652999
  have hstable : (prefixWord ++ tailWord_652999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652999).length < 2 ^ (prefixWord ++ tailWord_652999).sum := by decide
  have hdescent : baseEnd_652999 < baseStart_652999 := by decide
  rcases family_descends (prefixWord ++ tailWord_652999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653002 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_653002 : Nat := 118140960795 + 653002 * 2 ^ 59
def prefixEnd_653002 : Nat := 4983230072969 + 3 ^ 40 * 653002 * 2
def baseEnd_653002 : Nat := 298047906086541653663915

theorem tailTrace_653002 : CollatzResearch.WordTrace tailWord_653002 prefixEnd_653002 298047906086541653663915 := by
  unfold tailWord_653002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954234895073188176960315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15877959720195168471894173 5954234895073188176960315)
  ·
    refine ⟨8931352342609782265440473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954234895073188176960315 8931352342609782265440473)
    ·
      refine ⟨6698514256957336699080355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8931352342609782265440473 6698514256957336699080355)
      ·
        refine ⟨10047771385436005048620533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698514256957336699080355 10047771385436005048620533)
        ·
          refine ⟨941978567384625473308175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10047771385436005048620533 941978567384625473308175)
          ·
            refine ⟨1412967851076938209962263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941978567384625473308175 1412967851076938209962263)
            ·
              refine ⟨2119451776615407314943395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412967851076938209962263 2119451776615407314943395)
              ·
                refine ⟨3179177664923110972415093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119451776615407314943395 3179177664923110972415093)
                ·
                  refine ⟨298047906086541653663915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179177664923110972415093 298047906086541653663915)
                  ·
                    rfl

theorem cell20_653002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_653002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653002 prefixEnd_653002 := by exact prefixLift 653002
  have htrace : WordTrace (prefixWord ++ tailWord_653002) baseStart_653002 baseEnd_653002 := by
    simpa [prefixWord, tailWord_653002, baseEnd_653002] using wordTrace_append hprefix tailTrace_653002
  have hstable : (prefixWord ++ tailWord_653002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653002).length < 2 ^ (prefixWord ++ tailWord_653002).sum := by decide
  have hdescent : baseEnd_653002 < baseStart_653002 := by decide
  rcases family_descends (prefixWord ++ tailWord_653002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653005 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_653005 : Nat := 118140960795 + 653005 * 2 ^ 59
def prefixEnd_653005 : Nat := 4983230072969 + 3 ^ 40 * 653005 * 2
def baseEnd_653005 : Nat := 298049275368286976563903

theorem tailTrace_653005 : CollatzResearch.WordTrace tailWord_653005 prefixEnd_653005 298049275368286976563903 := by
  unfold tailWord_653005
  simp only [CollatzResearch.WordTrace]
  refine ⟨23817048999281884220200469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15878032666187922813466979 23817048999281884220200469)
  ·
    refine ⟨1116424171841338322821897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23817048999281884220200469 1116424171841338322821897)
    ·
      refine ⟨837318128881003742116423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116424171841338322821897 837318128881003742116423)
      ·
        refine ⟨1255977193321505613174635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837318128881003742116423 1255977193321505613174635)
        ·
          refine ⟨1883965789982258419761953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255977193321505613174635 1883965789982258419761953)
          ·
            refine ⟨1412974342486693814821465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883965789982258419761953 1412974342486693814821465)
            ·
              refine ⟨1059730756865020361116099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412974342486693814821465 1059730756865020361116099)
              ·
                refine ⟨1589596135297530541674149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059730756865020361116099 1589596135297530541674149)
                ·
                  refine ⟨298049275368286976563903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589596135297530541674149 298049275368286976563903)
                  ·
                    rfl

theorem cell20_653005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_653005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653005 prefixEnd_653005 := by exact prefixLift 653005
  have htrace : WordTrace (prefixWord ++ tailWord_653005) baseStart_653005 baseEnd_653005 := by
    simpa [prefixWord, tailWord_653005, baseEnd_653005] using wordTrace_append hprefix tailTrace_653005
  have hstable : (prefixWord ++ tailWord_653005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653005).length < 2 ^ (prefixWord ++ tailWord_653005).sum := by decide
  have hdescent : baseEnd_653005 < baseStart_653005 := by decide
  rcases family_descends (prefixWord ++ tailWord_653005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653009 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_653009 : Nat := 118140960795 + 653009 * 2 ^ 59
def prefixEnd_653009 : Nat := 4983230072969 + 3 ^ 40 * 653009 * 2
def baseEnd_653009 : Nat := 298051101077280740430553

theorem tailTrace_653009 : CollatzResearch.WordTrace tailWord_653009 prefixEnd_653009 298051101077280740430553 := by
  unfold tailWord_653009
  simp only [CollatzResearch.WordTrace]
  refine ⟨23817194891267392903346081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15878129927511595268897387 23817194891267392903346081)
  ·
    refine ⟨17862896168450544677509561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23817194891267392903346081 17862896168450544677509561)
    ·
      refine ⟨13397172126337908508132171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17862896168450544677509561 13397172126337908508132171)
      ·
        refine ⟨20095758189506862762198257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13397172126337908508132171 20095758189506862762198257)
        ·
          refine ⟨15071818642130147071648693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20095758189506862762198257 15071818642130147071648693)
          ·
            refine ⟨1412982997699701287967065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15071818642130147071648693 1412982997699701287967065)
            ·
              refine ⟨1059737248274775965975299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412982997699701287967065 1059737248274775965975299)
              ·
                refine ⟨1589605872412163948962949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059737248274775965975299 1589605872412163948962949)
                ·
                  refine ⟨298051101077280740430553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589605872412163948962949 298051101077280740430553)
                  ·
                    rfl

theorem cell20_653009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_653009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653009 prefixEnd_653009 := by exact prefixLift 653009
  have htrace : WordTrace (prefixWord ++ tailWord_653009) baseStart_653009 baseEnd_653009 := by
    simpa [prefixWord, tailWord_653009, baseEnd_653009] using wordTrace_append hprefix tailTrace_653009
  have hstable : (prefixWord ++ tailWord_653009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653009).length < 2 ^ (prefixWord ++ tailWord_653009).sum := by decide
  have hdescent : baseEnd_653009 < baseStart_653009 := by decide
  rcases family_descends (prefixWord ++ tailWord_653009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653074 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_653074 : Nat := 118140960795 + 653074 * 2 ^ 59
def prefixEnd_653074 : Nat := 4983230072969 + 3 ^ 40 * 653074 * 2
def baseEnd_653074 : Nat := 298080768848429403263621

theorem tailTrace_653074 : CollatzResearch.WordTrace tailWord_653074 prefixEnd_653074 298080768848429403263621 := by
  unfold tailWord_653074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954891409007977251115569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15879710424021272669641517 5954891409007977251115569)
  ·
    refine ⟨4466168556755982938336677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5954891409007977251115569 4466168556755982938336677)
    ·
      refine ⟨837406604391746800938127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4466168556755982938336677 837406604391746800938127)
      ·
        refine ⟨1256109906587620201407191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837406604391746800938127 1256109906587620201407191)
        ·
          refine ⟨1884164859881430302110787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256109906587620201407191 1884164859881430302110787)
          ·
            refine ⟨2826247289822145453166181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884164859881430302110787 2826247289822145453166181)
            ·
              refine ⟨529921366841652272468659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2826247289822145453166181 529921366841652272468659)
              ·
                refine ⟨794882050262478408702989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529921366841652272468659 794882050262478408702989)
                ·
                  refine ⟨298080768848429403263621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794882050262478408702989 298080768848429403263621)
                  ·
                    rfl

theorem cell20_653074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_653074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653074 prefixEnd_653074 := by exact prefixLift 653074
  have htrace : WordTrace (prefixWord ++ tailWord_653074) baseStart_653074 baseEnd_653074 := by
    simpa [prefixWord, tailWord_653074, baseEnd_653074] using wordTrace_append hprefix tailTrace_653074
  have hstable : (prefixWord ++ tailWord_653074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653074).length < 2 ^ (prefixWord ++ tailWord_653074).sum := by decide
  have hdescent : baseEnd_653074 < baseStart_653074 := by decide
  rcases family_descends (prefixWord ++ tailWord_653074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653092 : List Nat := [2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_653092 : Nat := 118140960795 + 653092 * 2 ^ 59
def prefixEnd_653092 : Nat := 4983230072969 + 3 ^ 40 * 653092 * 2
def baseEnd_653092 : Nat := 99362994846300446887849

theorem tailTrace_653092 : CollatzResearch.WordTrace tailWord_653092 prefixEnd_653092 99362994846300446887849 := by
  unfold tailWord_653092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910111074983349039308765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15880148099977798719078353 11910111074983349039308765)
  ·
    refine ⟨4466291653118755889740787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11910111074983349039308765 4466291653118755889740787)
    ·
      refine ⟨6699437479678133834611181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466291653118755889740787 6699437479678133834611181)
      ·
        refine ⟨2512289054879300187979193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6699437479678133834611181 2512289054879300187979193)
        ·
          refine ⟨1884216791159475140984395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512289054879300187979193 1884216791159475140984395)
          ·
            refine ⟨2826325186739212711476593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884216791159475140984395 2826325186739212711476593)
            ·
              refine ⟨2119743890054409533607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2826325186739212711476593 2119743890054409533607445)
              ·
                refine ⟨99362994846300446887849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2119743890054409533607445 99362994846300446887849)
                ·
                  rfl

theorem cell20_653092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_653092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653092 prefixEnd_653092 := by exact prefixLift 653092
  have htrace : WordTrace (prefixWord ++ tailWord_653092) baseStart_653092 baseEnd_653092 := by
    simpa [prefixWord, tailWord_653092, baseEnd_653092] using wordTrace_append hprefix tailTrace_653092
  have hstable : (prefixWord ++ tailWord_653092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653092).length < 2 ^ (prefixWord ++ tailWord_653092).sum := by decide
  have hdescent : baseEnd_653092 < baseStart_653092 := by decide
  rcases family_descends (prefixWord ++ tailWord_653092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653126 : List Nat := [6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_653126 : Nat := 118140960795 + 653126 * 2 ^ 59
def prefixEnd_653126 : Nat := 4983230072969 + 3 ^ 40 * 653126 * 2
def baseEnd_653126 : Nat := 99368167688449444510025

theorem tailTrace_653126 : CollatzResearch.WordTrace tailWord_653126 prefixEnd_653126 99368167688449444510025 := by
  unfold tailWord_653126
  simp only [CollatzResearch.WordTrace]
  refine ⟨744420694745110058917351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15880974821229014590236821 744420694745110058917351)
  ·
    refine ⟨1116631042117665088376027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744420694745110058917351 1116631042117665088376027)
    ·
      refine ⟨1674946563176497632564041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116631042117665088376027 1674946563176497632564041)
      ·
        refine ⟨1256209922382373224423031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674946563176497632564041 1256209922382373224423031)
        ·
          refine ⟨1884314883573559836634547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256209922382373224423031 1884314883573559836634547)
          ·
            refine ⟨2826472325360339754951821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884314883573559836634547 2826472325360339754951821)
            ·
              refine ⟨1059927122010127408106933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2826472325360339754951821 1059927122010127408106933)
              ·
                refine ⟨99368167688449444510025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059927122010127408106933 99368167688449444510025)
                ·
                  rfl

theorem cell20_653126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_653126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653126 prefixEnd_653126 := by exact prefixLift 653126
  have htrace : WordTrace (prefixWord ++ tailWord_653126) baseStart_653126 baseEnd_653126 := by
    simpa [prefixWord, tailWord_653126, baseEnd_653126] using wordTrace_append hprefix tailTrace_653126
  have hstable : (prefixWord ++ tailWord_653126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653126).length < 2 ^ (prefixWord ++ tailWord_653126).sum := by decide
  have hdescent : baseEnd_653126 < baseStart_653126 := by decide
  rcases family_descends (prefixWord ++ tailWord_653126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653133 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_653133 : Nat := 118140960795 + 653133 * 2 ^ 59
def prefixEnd_653133 : Nat := 4983230072969 + 3 ^ 40 * 653133 * 2
def baseEnd_653133 : Nat := 298107698056087420296713

theorem tailTrace_653133 : CollatzResearch.WordTrace tailWord_653133 prefixEnd_653133 298107698056087420296713 := by
  unfold tailWord_653133
  simp only [CollatzResearch.WordTrace]
  refine ⟨23821717542818162080860053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15881145028545441387240035 23821717542818162080860053)
  ·
    refine ⟨1116643009819601347540315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23821717542818162080860053 1116643009819601347540315)
    ·
      refine ⟨1674964514729402021310473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116643009819601347540315 1674964514729402021310473)
      ·
        refine ⟨1256223386047051515982855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674964514729402021310473 1256223386047051515982855)
        ·
          refine ⟨1884335079070577273974283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256223386047051515982855 1884335079070577273974283)
          ·
            refine ⟨2826502618605865910961425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884335079070577273974283 2826502618605865910961425)
            ·
              refine ⟨2119876963954399433221069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2826502618605865910961425 2119876963954399433221069)
              ·
                refine ⟨794953861482899787457901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2119876963954399433221069 794953861482899787457901)
                ·
                  refine ⟨298107698056087420296713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794953861482899787457901 298107698056087420296713)
                  ·
                    rfl

theorem cell20_653133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_653133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653133 prefixEnd_653133 := by exact prefixLift 653133
  have htrace : WordTrace (prefixWord ++ tailWord_653133) baseStart_653133 baseEnd_653133 := by
    simpa [prefixWord, tailWord_653133, baseEnd_653133] using wordTrace_append hprefix tailTrace_653133
  have hstable : (prefixWord ++ tailWord_653133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653133).length < 2 ^ (prefixWord ++ tailWord_653133).sum := by decide
  have hdescent : baseEnd_653133 < baseStart_653133 := by decide
  rcases family_descends (prefixWord ++ tailWord_653133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653189 : List Nat := [1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_653189 : Nat := 118140960795 + 653189 * 2 ^ 59
def prefixEnd_653189 : Nat := 4983230072969 + 3 ^ 40 * 653189 * 2
def baseEnd_653189 : Nat := 99377752660666704809939

theorem tailTrace_653189 : CollatzResearch.WordTrace tailWord_653189 prefixEnd_653189 99377752660666704809939 := by
  unfold tailWord_653189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23823760030615283644898621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15882506687076855763265747 23823760030615283644898621)
  ·
    refine ⟨8933910011480731366836983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23823760030615283644898621 8933910011480731366836983)
    ·
      refine ⟨13400865017221097050255475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933910011480731366836983 13400865017221097050255475)
      ·
        refine ⟨20101297525831645575383213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13400865017221097050255475 20101297525831645575383213)
        ·
          refine ⟨7537986572186867090768705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20101297525831645575383213 7537986572186867090768705)
          ·
            refine ⟨5653489929140150318076529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537986572186867090768705 5653489929140150318076529)
            ·
              refine ⟨4240117446855112738557397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653489929140150318076529 4240117446855112738557397)
              ·
                refine ⟨99377752660666704809939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4240117446855112738557397 99377752660666704809939)
                ·
                  rfl

theorem cell20_653189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_653189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653189 prefixEnd_653189 := by exact prefixLift 653189
  have htrace : WordTrace (prefixWord ++ tailWord_653189) baseStart_653189 baseEnd_653189 := by
    simpa [prefixWord, tailWord_653189, baseEnd_653189] using wordTrace_append hprefix tailTrace_653189
  have hstable : (prefixWord ++ tailWord_653189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653189).length < 2 ^ (prefixWord ++ tailWord_653189).sum := by decide
  have hdescent : baseEnd_653189 < baseStart_653189 := by decide
  rcases family_descends (prefixWord ++ tailWord_653189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653202 : List Nat := [3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_653202 : Nat := 118140960795 + 653202 * 2 ^ 59
def prefixEnd_653202 : Nat := 4983230072969 + 3 ^ 40 * 653202 * 2
def baseEnd_653202 : Nat := 99379730512076615665477

theorem tailTrace_653202 : CollatzResearch.WordTrace tailWord_653202 prefixEnd_653202 99379730512076615665477 := by
  unfold tailWord_653202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956058544892046716280465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15882822786378791243414573 5956058544892046716280465)
  ·
    refine ⟨4467043908669035037210349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5956058544892046716280465 4467043908669035037210349)
    ·
      refine ⟨1675141465750888138953881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4467043908669035037210349 1675141465750888138953881)
      ·
        refine ⟨1256356099313166104215411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1675141465750888138953881 1256356099313166104215411)
        ·
          refine ⟨1884534148969749156323117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256356099313166104215411 1884534148969749156323117)
          ·
            refine ⟨706700305863655933621169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1884534148969749156323117 706700305863655933621169)
            ·
              refine ⟨530025229397741950215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706700305863655933621169 530025229397741950215877)
              ·
                refine ⟨99379730512076615665477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530025229397741950215877 99379730512076615665477)
                ·
                  rfl

theorem cell20_653202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_653202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653202 prefixEnd_653202 := by exact prefixLift 653202
  have htrace : WordTrace (prefixWord ++ tailWord_653202) baseStart_653202 baseEnd_653202 := by
    simpa [prefixWord, tailWord_653202, baseEnd_653202] using wordTrace_append hprefix tailTrace_653202
  have hstable : (prefixWord ++ tailWord_653202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653202).length < 2 ^ (prefixWord ++ tailWord_653202).sum := by decide
  have hdescent : baseEnd_653202 < baseStart_653202 := by decide
  rcases family_descends (prefixWord ++ tailWord_653202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653213 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_653213 : Nat := 118140960795 + 653213 * 2 ^ 59
def prefixEnd_653213 : Nat := 4983230072969 + 3 ^ 40 * 653213 * 2
def baseEnd_653213 : Nat := 298144212235962697629719

theorem tailTrace_653213 : CollatzResearch.WordTrace tailWord_653213 prefixEnd_653213 298144212235962697629719 := by
  unfold tailWord_653213
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824635382528335743772293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15883090255018890495848195 23824635382528335743772293)
  ·
    refine ⟨4467119134224062951957305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23824635382528335743772293 4467119134224062951957305)
    ·
      refine ⟨3350339350668047213967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4467119134224062951957305 3350339350668047213967979)
      ·
        refine ⟨5025509026002070820951969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350339350668047213967979 5025509026002070820951969)
        ·
          refine ⟨3769131769501553115713977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5025509026002070820951969 3769131769501553115713977)
          ·
            refine ⟨2826848827126164836785483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769131769501553115713977 2826848827126164836785483)
            ·
              refine ⟨4240273240689247255178225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826848827126164836785483 4240273240689247255178225)
              ·
                refine ⟨3180204930516935441383669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4240273240689247255178225 3180204930516935441383669)
                ·
                  refine ⟨298144212235962697629719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180204930516935441383669 298144212235962697629719)
                  ·
                    rfl

theorem cell20_653213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_653213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653213 prefixEnd_653213 := by exact prefixLift 653213
  have htrace : WordTrace (prefixWord ++ tailWord_653213) baseStart_653213 baseEnd_653213 := by
    simpa [prefixWord, tailWord_653213, baseEnd_653213] using wordTrace_append hprefix tailTrace_653213
  have hstable : (prefixWord ++ tailWord_653213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653213).length < 2 ^ (prefixWord ++ tailWord_653213).sum := by decide
  have hdescent : baseEnd_653213 < baseStart_653213 := by decide
  rcases family_descends (prefixWord ++ tailWord_653213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653233 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 2]
def baseStart_653233 : Nat := 118140960795 + 653233 * 2 ^ 59
def prefixEnd_653233 : Nat := 4983230072969 + 3 ^ 40 * 653233 * 2
def baseEnd_653233 : Nat := 298153340780931516962971

theorem tailTrace_653233 : CollatzResearch.WordTrace tailWord_653233 prefixEnd_653233 298153340780931516962971 := by
  unfold tailWord_653233
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825364842455879159500353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15883576561637252773000235 23825364842455879159500353)
  ·
    refine ⟨17869023631841909369625265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23825364842455879159500353 17869023631841909369625265)
    ·
      refine ⟨13401767723881432027218949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17869023631841909369625265 13401767723881432027218949)
      ·
        refine ⟨2512831448227768505103553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13401767723881432027218949 2512831448227768505103553)
        ·
          refine ⟨1884623586170826378827665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512831448227768505103553 1884623586170826378827665)
          ·
            refine ⟨1413467689628119784120749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1884623586170826378827665 1413467689628119784120749)
            ·
              refine ⟨530050383610544919045281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413467689628119784120749 530050383610544919045281)
              ·
                refine ⟨397537787707908689283961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530050383610544919045281 397537787707908689283961)
                ·
                  refine ⟨298153340780931516962971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397537787707908689283961 298153340780931516962971)
                  ·
                    rfl

theorem cell20_653233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_653233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653233 prefixEnd_653233 := by exact prefixLift 653233
  have htrace : WordTrace (prefixWord ++ tailWord_653233) baseStart_653233 baseEnd_653233 := by
    simpa [prefixWord, tailWord_653233, baseEnd_653233] using wordTrace_append hprefix tailTrace_653233
  have hstable : (prefixWord ++ tailWord_653233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653233).length < 2 ^ (prefixWord ++ tailWord_653233).sum := by decide
  have hdescent : baseEnd_653233 < baseStart_653233 := by decide
  rcases family_descends (prefixWord ++ tailWord_653233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653237 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_653237 : Nat := 118140960795 + 653237 * 2 ^ 59
def prefixEnd_653237 : Nat := 4983230072969 + 3 ^ 40 * 653237 * 2
def baseEnd_653237 : Nat := 298155166489925280829621

theorem tailTrace_653237 : CollatzResearch.WordTrace tailWord_653237 prefixEnd_653237 298155166489925280829621 := by
  unfold tailWord_653237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825510734441387842645965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15883673822960925228430643 23825510734441387842645965)
  ·
    refine ⟨8934566525415520440992237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23825510734441387842645965 8934566525415520440992237)
    ·
      refine ⟨3350462447030820165372089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8934566525415520440992237 3350462447030820165372089)
      ·
        refine ⟨2512846835273115124029067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350462447030820165372089 2512846835273115124029067)
        ·
          refine ⟨3769270252909672686043601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512846835273115124029067 3769270252909672686043601)
          ·
            refine ⟨2826952689682254514532701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769270252909672686043601 2826952689682254514532701)
            ·
              refine ⟨1060107258630845442949763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2826952689682254514532701 1060107258630845442949763)
              ·
                refine ⟨1590160887946268164424645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060107258630845442949763 1590160887946268164424645)
                ·
                  refine ⟨298155166489925280829621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590160887946268164424645 298155166489925280829621)
                  ·
                    rfl

theorem cell20_653237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_653237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653237 prefixEnd_653237 := by exact prefixLift 653237
  have htrace : WordTrace (prefixWord ++ tailWord_653237) baseStart_653237 baseEnd_653237 := by
    simpa [prefixWord, tailWord_653237, baseEnd_653237] using wordTrace_append hprefix tailTrace_653237
  have hstable : (prefixWord ++ tailWord_653237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653237).length < 2 ^ (prefixWord ++ tailWord_653237).sum := by decide
  have hdescent : baseEnd_653237 < baseStart_653237 := by decide
  rcases family_descends (prefixWord ++ tailWord_653237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653258 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_653258 : Nat := 118140960795 + 653258 * 2 ^ 59
def prefixEnd_653258 : Nat := 4983230072969 + 3 ^ 40 * 653258 * 2
def baseEnd_653258 : Nat := 298164751462142541129535

theorem tailTrace_653258 : CollatzResearch.WordTrace tailWord_653258 prefixEnd_653258 298164751462142541129535 := by
  unfold tailWord_653258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956569166841327107290107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15884184444910205619440285 5956569166841327107290107)
  ·
    refine ⟨8934853750261990660935161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5956569166841327107290107 8934853750261990660935161)
    ·
      refine ⟨6701140312696492995701371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8934853750261990660935161 6701140312696492995701371)
      ·
        refine ⟨10051710469044739493552057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701140312696492995701371 10051710469044739493552057)
        ·
          refine ⟨7538782851783554620164043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10051710469044739493552057 7538782851783554620164043)
          ·
            refine ⟨11308174277675331930246065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7538782851783554620164043 11308174277675331930246065)
            ·
              refine ⟨8481130708256498947684549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11308174277675331930246065 8481130708256498947684549)
              ·
                refine ⟨1590212007798093552690853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8481130708256498947684549 1590212007798093552690853)
                ·
                  refine ⟨298164751462142541129535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590212007798093552690853 298164751462142541129535)
                  ·
                    rfl

theorem cell20_653258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_653258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653258 prefixEnd_653258 := by exact prefixLift 653258
  have htrace : WordTrace (prefixWord ++ tailWord_653258) baseStart_653258 baseEnd_653258 := by
    simpa [prefixWord, tailWord_653258, baseEnd_653258] using wordTrace_append hprefix tailTrace_653258
  have hstable : (prefixWord ++ tailWord_653258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653258).length < 2 ^ (prefixWord ++ tailWord_653258).sum := by decide
  have hdescent : baseEnd_653258 < baseStart_653258 := by decide
  rcases family_descends (prefixWord ++ tailWord_653258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653282 : List Nat := [3, 3, 3, 1, 10]
def baseStart_653282 : Nat := 118140960795 + 653282 * 2 ^ 59
def prefixEnd_653282 : Nat := 4983230072969 + 3 ^ 40 * 653282 * 2
def baseEnd_653282 : Nat := 3681181552050680547277

theorem tailTrace_653282 : CollatzResearch.WordTrace tailWord_653282 prefixEnd_653282 3681181552050680547277 := by
  unfold tailWord_653282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956788004819590132008525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15884768012852240352022733 5956788004819590132008525)
  ·
    refine ⟨2233795501807346299503197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5956788004819590132008525 2233795501807346299503197)
    ·
      refine ⟨837673313177754862313699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2233795501807346299503197 837673313177754862313699)
      ·
        refine ⟨1256509969766632293470549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837673313177754862313699 1256509969766632293470549)
        ·
          refine ⟨3681181552050680547277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1256509969766632293470549 3681181552050680547277)
          ·
            rfl

theorem cell20_653282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 10].length) (baseStart_653282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653282 prefixEnd_653282 := by exact prefixLift 653282
  have htrace : WordTrace (prefixWord ++ tailWord_653282) baseStart_653282 baseEnd_653282 := by
    simpa [prefixWord, tailWord_653282, baseEnd_653282] using wordTrace_append hprefix tailTrace_653282
  have hstable : (prefixWord ++ tailWord_653282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653282).length < 2 ^ (prefixWord ++ tailWord_653282).sum := by decide
  have hdescent : baseEnd_653282 < baseStart_653282 := by decide
  rcases family_descends (prefixWord ++ tailWord_653282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653316 : List Nat := [2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_653316 : Nat := 118140960795 + 653316 * 2 ^ 59
def prefixEnd_653316 : Nat := 4983230072969 + 3 ^ 40 * 653316 * 2
def baseEnd_653316 : Nat := 99397074747517372398655

theorem tailTrace_653316 : CollatzResearch.WordTrace tailWord_653316 prefixEnd_653316 99397074747517372398655 := by
  unfold tailWord_653316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11914196050577592167385901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15885594734103456223181201 11914196050577592167385901)
  ·
    refine ⟨4467823518966597062769713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11914196050577592167385901 4467823518966597062769713)
    ·
      refine ⟨3350867639224947797077285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4467823518966597062769713 3350867639224947797077285)
      ·
        refine ⟨628287682354677711951991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3350867639224947797077285 628287682354677711951991)
        ·
          refine ⟨942431523532016567927987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628287682354677711951991 942431523532016567927987)
          ·
            refine ⟨1413647285298024851891981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942431523532016567927987 1413647285298024851891981)
            ·
              refine ⟨530117731986759319459493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413647285298024851891981 530117731986759319459493)
              ·
                refine ⟨99397074747517372398655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530117731986759319459493 99397074747517372398655)
                ·
                  rfl

theorem cell20_653316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_653316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653316 prefixEnd_653316 := by exact prefixLift 653316
  have htrace : WordTrace (prefixWord ++ tailWord_653316) baseStart_653316 baseEnd_653316 := by
    simpa [prefixWord, tailWord_653316, baseEnd_653316] using wordTrace_append hprefix tailTrace_653316
  have hstable : (prefixWord ++ tailWord_653316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653316).length < 2 ^ (prefixWord ++ tailWord_653316).sum := by decide
  have hdescent : baseEnd_653316 < baseStart_653316 := by decide
  rcases family_descends (prefixWord ++ tailWord_653316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653320 : List Nat := [2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_653320 : Nat := 118140960795 + 653320 * 2 ^ 59
def prefixEnd_653320 : Nat := 4983230072969 + 3 ^ 40 * 653320 * 2
def baseEnd_653320 : Nat := 99397683317181960354205

theorem tailTrace_653320 : CollatzResearch.WordTrace tailWord_653320 prefixEnd_653320 99397683317181960354205 := by
  unfold tailWord_653320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11914268996570346508958707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15885691995427128678611609 11914268996570346508958707)
  ·
    refine ⟨17871403494855519763438061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11914268996570346508958707 17871403494855519763438061)
    ·
      refine ⟨6701776310570819911289273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17871403494855519763438061 6701776310570819911289273)
      ·
        refine ⟨5026332232928114933466955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6701776310570819911289273 5026332232928114933466955)
        ·
          refine ⟨7539498349392172400200433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026332232928114933466955 7539498349392172400200433)
          ·
            refine ⟨5654623762044129300150325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7539498349392172400200433 5654623762044129300150325)
            ·
              refine ⟨530120977691637121889093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5654623762044129300150325 530120977691637121889093)
              ·
                refine ⟨99397683317181960354205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530120977691637121889093 99397683317181960354205)
                ·
                  rfl

theorem cell20_653320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_653320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653320 prefixEnd_653320 := by exact prefixLift 653320
  have htrace : WordTrace (prefixWord ++ tailWord_653320) baseStart_653320 baseEnd_653320 := by
    simpa [prefixWord, tailWord_653320, baseEnd_653320] using wordTrace_append hprefix tailTrace_653320
  have hstable : (prefixWord ++ tailWord_653320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653320).length < 2 ^ (prefixWord ++ tailWord_653320).sum := by decide
  have hdescent : baseEnd_653320 < baseStart_653320 := by decide
  rcases family_descends (prefixWord ++ tailWord_653320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653365 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_653365 : Nat := 118140960795 + 653365 * 2 ^ 59
def prefixEnd_653365 : Nat := 4983230072969 + 3 ^ 40 * 653365 * 2
def baseEnd_653365 : Nat := 298213589177725724562431

theorem tailTrace_653365 : CollatzResearch.WordTrace tailWord_653365 prefixEnd_653365 298213589177725724562431 := by
  unfold tailWord_653365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830179277977665703305549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15886786185318443802203699 23830179277977665703305549)
  ·
    refine ⟨8936317229241624638739581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23830179277977665703305549 8936317229241624638739581)
    ·
      refine ⟨3351118960965609239527343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8936317229241624638739581 3351118960965609239527343)
      ·
        refine ⟨5026678441448413859291015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351118960965609239527343 5026678441448413859291015)
        ·
          refine ⟨7540017662172620788936523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026678441448413859291015 7540017662172620788936523)
          ·
            refine ⟨11310026493258931183404785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540017662172620788936523 11310026493258931183404785)
            ·
              refine ⟨8482519869944198387553589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11310026493258931183404785 8482519869944198387553589)
              ·
                refine ⟨795236237807268598833149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8482519869944198387553589 795236237807268598833149)
                ·
                  refine ⟨298213589177725724562431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795236237807268598833149 298213589177725724562431)
                  ·
                    rfl

theorem cell20_653365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_653365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653365 prefixEnd_653365 := by exact prefixLift 653365
  have htrace : WordTrace (prefixWord ++ tailWord_653365) baseStart_653365 baseEnd_653365 := by
    simpa [prefixWord, tailWord_653365, baseEnd_653365] using wordTrace_append hprefix tailTrace_653365
  have hstable : (prefixWord ++ tailWord_653365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653365).length < 2 ^ (prefixWord ++ tailWord_653365).sum := by decide
  have hdescent : baseEnd_653365 < baseStart_653365 := by decide
  rcases family_descends (prefixWord ++ tailWord_653365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653372 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_653372 : Nat := 118140960795 + 653372 * 2 ^ 59
def prefixEnd_653372 : Nat := 4983230072969 + 3 ^ 40 * 653372 * 2
def baseEnd_653372 : Nat := 298216784168464811329069

theorem tailTrace_653372 : CollatzResearch.WordTrace tailWord_653372 prefixEnd_653372 298216784168464811329069 := by
  unfold tailWord_653372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915217294476152949405185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15886956392634870599206913 11915217294476152949405185)
  ·
    refine ⟨8936412970857114712053889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11915217294476152949405185 8936412970857114712053889)
    ·
      refine ⟨6702309728142836034040417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8936412970857114712053889 6702309728142836034040417)
      ·
        refine ⟨5026732296107127025530313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6702309728142836034040417 5026732296107127025530313)
        ·
          refine ⟨3770049222080345269147735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5026732296107127025530313 3770049222080345269147735)
          ·
            refine ⟨5655073833120517903721603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770049222080345269147735 5655073833120517903721603)
            ·
              refine ⟨8482610749680776855582405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655073833120517903721603 8482610749680776855582405)
              ·
                refine ⟨1590489515565145660421701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8482610749680776855582405 1590489515565145660421701)
                ·
                  refine ⟨298216784168464811329069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590489515565145660421701 298216784168464811329069)
                  ·
                    rfl

theorem cell20_653372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_653372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653372 prefixEnd_653372 := by exact prefixLift 653372
  have htrace : WordTrace (prefixWord ++ tailWord_653372) baseStart_653372 baseEnd_653372 := by
    simpa [prefixWord, tailWord_653372, baseEnd_653372] using wordTrace_append hprefix tailTrace_653372
  have hstable : (prefixWord ++ tailWord_653372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653372).length < 2 ^ (prefixWord ++ tailWord_653372).sum := by decide
  have hdescent : baseEnd_653372 < baseStart_653372 := by decide
  rcases family_descends (prefixWord ++ tailWord_653372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653382 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_653382 : Nat := 118140960795 + 653382 * 2 ^ 59
def prefixEnd_653382 : Nat := 4983230072969 + 3 ^ 40 * 653382 * 2
def baseEnd_653382 : Nat := 298221348440949220995695

theorem tailTrace_653382 : CollatzResearch.WordTrace tailWord_653382 prefixEnd_653382 298221348440949220995695 := by
  unfold tailWord_653382
  simp only [CollatzResearch.WordTrace]
  refine ⟨744712478716127425208575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15887199545944051737782933 744712478716127425208575)
  ·
    refine ⟨1117068718074191137812863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744712478716127425208575 1117068718074191137812863)
    ·
      refine ⟨1675603077111286706719295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117068718074191137812863 1675603077111286706719295)
      ·
        refine ⟨2513404615666930060078943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675603077111286706719295 2513404615666930060078943)
        ·
          refine ⟨3770106923500395090118415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513404615666930060078943 3770106923500395090118415)
          ·
            refine ⟨5655160385250592635177623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770106923500395090118415 5655160385250592635177623)
            ·
              refine ⟨8482740577875888952766435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655160385250592635177623 8482740577875888952766435)
              ·
                refine ⟨12724110866813833429149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8482740577875888952766435 12724110866813833429149653)
                ·
                  refine ⟨298221348440949220995695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12724110866813833429149653 298221348440949220995695)
                  ·
                    rfl

theorem cell20_653382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_653382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653382 prefixEnd_653382 := by exact prefixLift 653382
  have htrace : WordTrace (prefixWord ++ tailWord_653382) baseStart_653382 baseEnd_653382 := by
    simpa [prefixWord, tailWord_653382, baseEnd_653382] using wordTrace_append hprefix tailTrace_653382
  have hstable : (prefixWord ++ tailWord_653382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653382).length < 2 ^ (prefixWord ++ tailWord_653382).sum := by decide
  have hdescent : baseEnd_653382 < baseStart_653382 := by decide
  rcases family_descends (prefixWord ++ tailWord_653382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653417 : List Nat := [1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_653417 : Nat := 118140960795 + 653417 * 2 ^ 59
def prefixEnd_653417 : Nat := 4983230072969 + 3 ^ 40 * 653417 * 2
def baseEnd_653417 : Nat := 99412441131548218276295

theorem tailTrace_653417 : CollatzResearch.WordTrace tailWord_653417 prefixEnd_653417 99412441131548218276295 := by
  unfold tailWord_653417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832075873789278584198505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15888050582526185722799003 23832075873789278584198505)
  ·
    refine ⟨17874056905341958938148879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23832075873789278584198505 17874056905341958938148879)
    ·
      refine ⟨26811085358012938407223319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17874056905341958938148879 26811085358012938407223319)
      ·
        refine ⟨40216628037019407610834979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26811085358012938407223319 40216628037019407610834979)
        ·
          refine ⟨60324942055529111416252469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40216628037019407610834979 60324942055529111416252469)
          ·
            refine ⟨5655463317705854195273669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60324942055529111416252469 5655463317705854195273669)
            ·
              refine ⟨1060399372069847661613813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5655463317705854195273669 1060399372069847661613813)
              ·
                refine ⟨99412441131548218276295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1060399372069847661613813 99412441131548218276295)
                ·
                  rfl

theorem cell20_653417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_653417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653417 prefixEnd_653417 := by exact prefixLift 653417
  have htrace : WordTrace (prefixWord ++ tailWord_653417) baseStart_653417 baseEnd_653417 := by
    simpa [prefixWord, tailWord_653417, baseEnd_653417] using wordTrace_append hprefix tailTrace_653417
  have hstable : (prefixWord ++ tailWord_653417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653417).length < 2 ^ (prefixWord ++ tailWord_653417).sum := by decide
  have hdescent : baseEnd_653417 < baseStart_653417 := by decide
  rcases family_descends (prefixWord ++ tailWord_653417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653420 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_653420 : Nat := 118140960795 + 653420 * 2 ^ 59
def prefixEnd_653420 : Nat := 4983230072969 + 3 ^ 40 * 653420 * 2
def baseEnd_653420 : Nat := 298238692676389977728873

theorem tailTrace_653420 : CollatzResearch.WordTrace tailWord_653420 prefixEnd_653420 298238692676389977728873 := by
  unfold tailWord_653420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916092646389205048278857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15888123528518940064371809 11916092646389205048278857)
  ·
    refine ⟨8937069484791903786209143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11916092646389205048278857 8937069484791903786209143)
    ·
      refine ⟨13405604227187855679313715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937069484791903786209143 13405604227187855679313715)
      ·
        refine ⟨20108406340781783518970573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405604227187855679313715 20108406340781783518970573)
        ·
          refine ⟨7540652377793168819613965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20108406340781783518970573 7540652377793168819613965)
          ·
            refine ⟨2827744641672438307355237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7540652377793168819613965 2827744641672438307355237)
            ·
              refine ⟨530202120313582182629107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2827744641672438307355237 530202120313582182629107)
              ·
                refine ⟨795303180470373273943661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530202120313582182629107 795303180470373273943661)
                ·
                  refine ⟨298238692676389977728873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795303180470373273943661 298238692676389977728873)
                  ·
                    rfl

theorem cell20_653420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_653420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653420 prefixEnd_653420 := by exact prefixLift 653420
  have htrace : WordTrace (prefixWord ++ tailWord_653420) baseStart_653420 baseEnd_653420 := by
    simpa [prefixWord, tailWord_653420, baseEnd_653420] using wordTrace_append hprefix tailTrace_653420
  have hstable : (prefixWord ++ tailWord_653420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653420).length < 2 ^ (prefixWord ++ tailWord_653420).sum := by decide
  have hdescent : baseEnd_653420 < baseStart_653420 := by decide
  rcases family_descends (prefixWord ++ tailWord_653420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653458 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_653458 : Nat := 118140960795 + 653458 * 2 ^ 59
def prefixEnd_653458 : Nat := 4983230072969 + 3 ^ 40 * 653458 * 2
def baseEnd_653458 : Nat := 298256036911830734462051

theorem tailTrace_653458 : CollatzResearch.WordTrace tailWord_653458 prefixEnd_653458 298256036911830734462051 := by
  unfold tailWord_653458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958392816660185646610257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15889047511093828390960685 5958392816660185646610257)
  ·
    refine ⟨4468794612495139234957693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5958392816660185646610257 4468794612495139234957693)
    ·
      refine ⟨1675797979685677213109135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4468794612495139234957693 1675797979685677213109135)
      ·
        refine ⟨2513696969528515819663703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675797979685677213109135 2513696969528515819663703)
        ·
          refine ⟨3770545454292773729495555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513696969528515819663703 3770545454292773729495555)
          ·
            refine ⟨5655818181439160594243333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770545454292773729495555 5655818181439160594243333)
            ·
              refine ⟨1060465909019842611420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5655818181439160594243333 1060465909019842611420625)
              ·
                refine ⟨795349431764881958565469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060465909019842611420625 795349431764881958565469)
                ·
                  refine ⟨298256036911830734462051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795349431764881958565469 298256036911830734462051)
                  ·
                    rfl

theorem cell20_653458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_653458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653458 prefixEnd_653458 := by exact prefixLift 653458
  have htrace : WordTrace (prefixWord ++ tailWord_653458) baseStart_653458 baseEnd_653458 := by
    simpa [prefixWord, tailWord_653458, baseEnd_653458] using wordTrace_append hprefix tailTrace_653458
  have hstable : (prefixWord ++ tailWord_653458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653458).length < 2 ^ (prefixWord ++ tailWord_653458).sum := by decide
  have hdescent : baseEnd_653458 < baseStart_653458 := by decide
  rcases family_descends (prefixWord ++ tailWord_653458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653472 : List Nat := [2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_653472 : Nat := 118140960795 + 653472 * 2 ^ 59
def prefixEnd_653472 : Nat := 4983230072969 + 3 ^ 40 * 653472 * 2
def baseEnd_653472 : Nat := 99420808964436302665109

theorem tailTrace_653472 : CollatzResearch.WordTrace tailWord_653472 prefixEnd_653472 99420808964436302665109 := by
  unfold tailWord_653472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917040944295011488725335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15889387925726681984967113 11917040944295011488725335)
  ·
    refine ⟨17875561416442517233088003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11917040944295011488725335 17875561416442517233088003)
    ·
      refine ⟨26813342124663775849632005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17875561416442517233088003 26813342124663775849632005)
      ·
        refine ⟨5027501648374457971806001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26813342124663775849632005 5027501648374457971806001)
        ·
          refine ⟨3770626236280843478854501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027501648374457971806001 3770626236280843478854501)
          ·
            refine ⟨706992419302658152285219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3770626236280843478854501 706992419302658152285219)
            ·
              refine ⟨1060488628953987228427829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706992419302658152285219 1060488628953987228427829)
              ·
                refine ⟨99420808964436302665109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1060488628953987228427829 99420808964436302665109)
                ·
                  rfl

theorem cell20_653472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_653472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653472 prefixEnd_653472 := by exact prefixLift 653472
  have htrace : WordTrace (prefixWord ++ tailWord_653472) baseStart_653472 baseEnd_653472 := by
    simpa [prefixWord, tailWord_653472, baseEnd_653472] using wordTrace_append hprefix tailTrace_653472
  have hstable : (prefixWord ++ tailWord_653472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653472).length < 2 ^ (prefixWord ++ tailWord_653472).sum := by decide
  have hdescent : baseEnd_653472 < baseStart_653472 := by decide
  rcases family_descends (prefixWord ++ tailWord_653472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653482 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_653482 : Nat := 118140960795 + 653482 * 2 ^ 59
def prefixEnd_653482 : Nat := 4983230072969 + 3 ^ 40 * 653482 * 2
def baseEnd_653482 : Nat := 298266991165793317661953

theorem tailTrace_653482 : CollatzResearch.WordTrace tailWord_653482 prefixEnd_653482 298266991165793317661953 := by
  unfold tailWord_653482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958611654638448671328675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15889631079035863123543133 5958611654638448671328675)
  ·
    refine ⟨8937917481957673006993013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958611654638448671328675 8937917481957673006993013)
    ·
      refine ⟨837929763933531844405595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8937917481957673006993013 837929763933531844405595)
      ·
        refine ⟨1256894645900297766608393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837929763933531844405595 1256894645900297766608393)
        ·
          refine ⟨942670984425223324956295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256894645900297766608393 942670984425223324956295)
          ·
            refine ⟨1414006476637834987434443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942670984425223324956295 1414006476637834987434443)
            ·
              refine ⟨2121009714956752481151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414006476637834987434443 2121009714956752481151665)
              ·
                refine ⟨1590757286217564360863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121009714956752481151665 1590757286217564360863749)
                ·
                  refine ⟨298266991165793317661953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590757286217564360863749 298266991165793317661953)
                  ·
                    rfl

theorem cell20_653482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_653482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653482 prefixEnd_653482 := by exact prefixLift 653482
  have htrace : WordTrace (prefixWord ++ tailWord_653482) baseStart_653482 baseEnd_653482 := by
    simpa [prefixWord, tailWord_653482, baseEnd_653482] using wordTrace_append hprefix tailTrace_653482
  have hstable : (prefixWord ++ tailWord_653482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653482).length < 2 ^ (prefixWord ++ tailWord_653482).sum := by decide
  have hdescent : baseEnd_653482 < baseStart_653482 := by decide
  rcases family_descends (prefixWord ++ tailWord_653482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653489 : List Nat := [1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_653489 : Nat := 118140960795 + 653489 * 2 ^ 59
def prefixEnd_653489 : Nat := 4983230072969 + 3 ^ 40 * 653489 * 2
def baseEnd_653489 : Nat := 99423395385510801476197

theorem tailTrace_653489 : CollatzResearch.WordTrace tailWord_653489 prefixEnd_653489 99423395385510801476197 := by
  unfold tailWord_653489
  simp only [CollatzResearch.WordTrace]
  refine ⟨23834701929528434880819521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15889801286352289920546347 23834701929528434880819521)
  ·
    refine ⟨17876026447146326160614641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23834701929528434880819521 17876026447146326160614641)
    ·
      refine ⟨13407019835359744620460981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17876026447146326160614641 13407019835359744620460981)
      ·
        refine ⟨1256908109564976058168217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13407019835359744620460981 1256908109564976058168217)
        ·
          refine ⟨942681082173732043626163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256908109564976058168217 942681082173732043626163)
          ·
            refine ⟨1414021623260598065439245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942681082173732043626163 1414021623260598065439245)
            ·
              refine ⟨530258108722724274539717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1414021623260598065439245 530258108722724274539717)
              ·
                refine ⟨99423395385510801476197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530258108722724274539717 99423395385510801476197)
                ·
                  rfl

theorem cell20_653489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_653489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653489 prefixEnd_653489 := by exact prefixLift 653489
  have htrace : WordTrace (prefixWord ++ tailWord_653489) baseStart_653489 baseEnd_653489 := by
    simpa [prefixWord, tailWord_653489, baseEnd_653489] using wordTrace_append hprefix tailTrace_653489
  have hstable : (prefixWord ++ tailWord_653489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653489).length < 2 ^ (prefixWord ++ tailWord_653489).sum := by decide
  have hdescent : baseEnd_653489 < baseStart_653489 := by decide
  rcases family_descends (prefixWord ++ tailWord_653489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653558 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_653558 : Nat := 118140960795 + 653558 * 2 ^ 59
def prefixEnd_653558 : Nat := 4983230072969 + 3 ^ 40 * 653558 * 2
def baseEnd_653558 : Nat := 298301679636674831128309

theorem tailTrace_653558 : CollatzResearch.WordTrace tailWord_653558 prefixEnd_653558 298301679636674831128309 := by
  unfold tailWord_653558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489826160392403729067583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15891479044185639776720885 1489826160392403729067583)
  ·
    refine ⟨2234739240588605593601375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489826160392403729067583 2234739240588605593601375)
    ·
      refine ⟨3352108860882908390402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234739240588605593601375 3352108860882908390402063)
      ·
        refine ⟨5028163291324362585603095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352108860882908390402063 5028163291324362585603095)
        ·
          refine ⟨7542244936986543878404643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028163291324362585603095 7542244936986543878404643)
          ·
            refine ⟨11313367405479815817606965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542244936986543878404643 11313367405479815817606965)
            ·
              refine ⟨1060628194263732732900653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11313367405479815817606965 1060628194263732732900653)
              ·
                refine ⟨397735572848899774837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060628194263732732900653 397735572848899774837745)
                ·
                  refine ⟨298301679636674831128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397735572848899774837745 298301679636674831128309)
                  ·
                    rfl

theorem cell20_653558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_653558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653558 prefixEnd_653558 := by exact prefixLift 653558
  have htrace : WordTrace (prefixWord ++ tailWord_653558) baseStart_653558 baseEnd_653558 := by
    simpa [prefixWord, tailWord_653558, baseEnd_653558] using wordTrace_append hprefix tailTrace_653558
  have hstable : (prefixWord ++ tailWord_653558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653558).length < 2 ^ (prefixWord ++ tailWord_653558).sum := by decide
  have hdescent : baseEnd_653558 < baseStart_653558 := by decide
  rcases family_descends (prefixWord ++ tailWord_653558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653575 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 4]
def baseStart_653575 : Nat := 118140960795 + 653575 * 2 ^ 59
def prefixEnd_653575 : Nat := 4983230072969 + 3 ^ 40 * 653575 * 2
def baseEnd_653575 : Nat := 298309438899898327561573

theorem tailTrace_653575 : CollatzResearch.WordTrace tailWord_653575 prefixEnd_653575 298309438899898327561573 := by
  unfold tailWord_653575
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837838607216871568450179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15891892404811247712300119 23837838607216871568450179)
  ·
    refine ⟨35756757910825307352675269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23837838607216871568450179 35756757910825307352675269)
    ·
      refine ⟨6704392108279745128626613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35756757910825307352675269 6704392108279745128626613)
      ·
        refine ⟨628536760151226105808745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6704392108279745128626613 628536760151226105808745)
        ·
          refine ⟨471402570113419579356559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628536760151226105808745 471402570113419579356559)
          ·
            refine ⟨707103855170129369034839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471402570113419579356559 707103855170129369034839)
            ·
              refine ⟨1060655782755194053552259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707103855170129369034839 1060655782755194053552259)
              ·
                refine ⟨1590983674132791080328389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060655782755194053552259 1590983674132791080328389)
                ·
                  refine ⟨298309438899898327561573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590983674132791080328389 298309438899898327561573)
                  ·
                    rfl

theorem cell20_653575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4].length) (baseStart_653575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653575 prefixEnd_653575 := by exact prefixLift 653575
  have htrace : WordTrace (prefixWord ++ tailWord_653575) baseStart_653575 baseEnd_653575 := by
    simpa [prefixWord, tailWord_653575, baseEnd_653575] using wordTrace_append hprefix tailTrace_653575
  have hstable : (prefixWord ++ tailWord_653575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653575).length < 2 ^ (prefixWord ++ tailWord_653575).sum := by decide
  have hdescent : baseEnd_653575 < baseStart_653575 := by decide
  rcases family_descends (prefixWord ++ tailWord_653575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653631 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_653631 : Nat := 118140960795 + 653631 * 2 ^ 59
def prefixEnd_653631 : Nat := 4983230072969 + 3 ^ 40 * 653631 * 2
def baseEnd_653631 : Nat := 298334998825811021694677

theorem tailTrace_653631 : CollatzResearch.WordTrace tailWord_653631 prefixEnd_653631 298334998825811021694677 := by
  unfold tailWord_653631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23839881095013993132488747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15893254063342662088325831 23839881095013993132488747)
  ·
    refine ⟨35759821642520989698733121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23839881095013993132488747 35759821642520989698733121)
    ·
      refine ⟨26819866231890742274049841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35759821642520989698733121 26819866231890742274049841)
      ·
        refine ⟨20114899673918056705537381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26819866231890742274049841 20114899673918056705537381)
        ·
          refine ⟨3771543688859635632288259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20114899673918056705537381 3771543688859635632288259)
          ·
            refine ⟨5657315533289453448432389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771543688859635632288259 5657315533289453448432389)
            ·
              refine ⟨1060746662491772521581073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5657315533289453448432389 1060746662491772521581073)
              ·
                refine ⟨795559996868829391185805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060746662491772521581073 795559996868829391185805)
                ·
                  refine ⟨298334998825811021694677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795559996868829391185805 298334998825811021694677)
                  ·
                    rfl

theorem cell20_653631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_653631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653631 prefixEnd_653631 := by exact prefixLift 653631
  have htrace : WordTrace (prefixWord ++ tailWord_653631) baseStart_653631 baseEnd_653631 := by
    simpa [prefixWord, tailWord_653631, baseEnd_653631] using wordTrace_append hprefix tailTrace_653631
  have hstable : (prefixWord ++ tailWord_653631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653631).length < 2 ^ (prefixWord ++ tailWord_653631).sum := by decide
  have hdescent : baseEnd_653631 < baseStart_653631 := by decide
  rcases family_descends (prefixWord ++ tailWord_653631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653672 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_653672 : Nat := 118140960795 + 653672 * 2 ^ 59
def prefixEnd_653672 : Nat := 4983230072969 + 3 ^ 40 * 653672 * 2
def baseEnd_653672 : Nat := 298353712342997101327843

theorem tailTrace_653672 : CollatzResearch.WordTrace tailWord_653672 prefixEnd_653672 298353712342997101327843 := by
  unfold tailWord_653672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920688243932728567365635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15894250991910304756487513 11920688243932728567365635)
  ·
    refine ⟨17881032365899092851048453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920688243932728567365635 17881032365899092851048453)
    ·
      refine ⟨3352693568606079909571585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17881032365899092851048453 3352693568606079909571585)
      ·
        refine ⟨2514520176454559932178689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3352693568606079909571585 2514520176454559932178689)
        ·
          refine ⟨1885890132340919949134017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514520176454559932178689 1885890132340919949134017)
          ·
            refine ⟨1414417599255689961850513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885890132340919949134017 1414417599255689961850513)
            ·
              refine ⟨1060813199441767471387885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414417599255689961850513 1060813199441767471387885)
              ·
                refine ⟨397804949790662801770457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060813199441767471387885 397804949790662801770457)
                ·
                  refine ⟨298353712342997101327843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397804949790662801770457 298353712342997101327843)
                  ·
                    rfl

theorem cell20_653672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_653672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653672 prefixEnd_653672 := by exact prefixLift 653672
  have htrace : WordTrace (prefixWord ++ tailWord_653672) baseStart_653672 baseEnd_653672 := by
    simpa [prefixWord, tailWord_653672, baseEnd_653672] using wordTrace_append hprefix tailTrace_653672
  have hstable : (prefixWord ++ tailWord_653672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653672).length < 2 ^ (prefixWord ++ tailWord_653672).sum := by decide
  have hdescent : baseEnd_653672 < baseStart_653672 := by decide
  rcases family_descends (prefixWord ++ tailWord_653672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653693 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 2]
def baseStart_653693 : Nat := 118140960795 + 653693 * 2 ^ 59
def prefixEnd_653693 : Nat := 4983230072969 + 3 ^ 40 * 653693 * 2
def baseEnd_653693 : Nat := 298363297315214361627757

theorem tailTrace_653693 : CollatzResearch.WordTrace tailWord_653693 prefixEnd_653693 298363297315214361627757 := by
  unfold tailWord_653693
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842142420789377721245733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15894761613859585147497155 23842142420789377721245733)
  ·
    refine ⟨4470401703898008322733575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23842142420789377721245733 4470401703898008322733575)
    ·
      refine ⟨6705602555847012484100363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470401703898008322733575 6705602555847012484100363)
      ·
        refine ⟨10058403833770518726150545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705602555847012484100363 10058403833770518726150545)
        ·
          refine ⟨7543802875327889044612909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10058403833770518726150545 7543802875327889044612909)
          ·
            refine ⟨2828926078247958391729841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7543802875327889044612909 2828926078247958391729841)
            ·
              refine ⟨2121694558685968793797381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828926078247958391729841 2121694558685968793797381)
              ·
                refine ⟨397817729753619148837009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2121694558685968793797381 397817729753619148837009)
                ·
                  refine ⟨298363297315214361627757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397817729753619148837009 298363297315214361627757)
                  ·
                    rfl

theorem cell20_653693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_653693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653693 prefixEnd_653693 := by exact prefixLift 653693
  have htrace : WordTrace (prefixWord ++ tailWord_653693) baseStart_653693 baseEnd_653693 := by
    simpa [prefixWord, tailWord_653693, baseEnd_653693] using wordTrace_append hprefix tailTrace_653693
  have hstable : (prefixWord ++ tailWord_653693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653693).length < 2 ^ (prefixWord ++ tailWord_653693).sum := by decide
  have hdescent : baseEnd_653693 < baseStart_653693 := by decide
  rcases family_descends (prefixWord ++ tailWord_653693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653728 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_653728 : Nat := 118140960795 + 653728 * 2 ^ 59
def prefixEnd_653728 : Nat := 4983230072969 + 3 ^ 40 * 653728 * 2
def baseEnd_653728 : Nat := 298379272268909795460947

theorem tailTrace_653728 : CollatzResearch.WordTrace tailWord_653728 prefixEnd_653728 298379272268909795460947 := by
  unfold tailWord_653728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921709487831289349384919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15895612650441719132513225 11921709487831289349384919)
  ·
    refine ⟨17882564231746934024077379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11921709487831289349384919 17882564231746934024077379)
    ·
      refine ⟨26823846347620401036116069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17882564231746934024077379 26823846347620401036116069)
      ·
        refine ⟨5029471190178825194271763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26823846347620401036116069 5029471190178825194271763)
        ·
          refine ⟨7544206785268237791407645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029471190178825194271763 7544206785268237791407645)
          ·
            refine ⟨2829077544475589171777867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7544206785268237791407645 2829077544475589171777867)
            ·
              refine ⟨4243616316713383757666801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829077544475589171777867 4243616316713383757666801)
              ·
                refine ⟨3182712237535037818250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4243616316713383757666801 3182712237535037818250101)
                ·
                  refine ⟨298379272268909795460947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182712237535037818250101 298379272268909795460947)
                  ·
                    rfl

theorem cell20_653728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_653728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653728 prefixEnd_653728 := by exact prefixLift 653728
  have htrace : WordTrace (prefixWord ++ tailWord_653728) baseStart_653728 baseEnd_653728 := by
    simpa [prefixWord, tailWord_653728, baseEnd_653728] using wordTrace_append hprefix tailTrace_653728
  have hstable : (prefixWord ++ tailWord_653728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653728).length < 2 ^ (prefixWord ++ tailWord_653728).sum := by decide
  have hdescent : baseEnd_653728 < baseStart_653728 := by decide
  rcases family_descends (prefixWord ++ tailWord_653728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653731 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 2]
def baseStart_653731 : Nat := 118140960795 + 653731 * 2 ^ 59
def prefixEnd_653731 : Nat := 4983230072969 + 3 ^ 40 * 653731 * 2
def baseEnd_653731 : Nat := 298380641550655118360935

theorem tailTrace_653731 : CollatzResearch.WordTrace tailWord_653731 prefixEnd_653731 298380641550655118360935 := by
  unfold tailWord_653731
  simp only [CollatzResearch.WordTrace]
  refine ⟨23843528394651710211129047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15895685596434473474086031 23843528394651710211129047)
  ·
    refine ⟨35765292591977565316693571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23843528394651710211129047 35765292591977565316693571)
    ·
      refine ⟨53647938887966347975040357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35765292591977565316693571 53647938887966347975040357)
      ·
        refine ⟨10058988541493690245320067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53647938887966347975040357 10058988541493690245320067)
        ·
          refine ⟨15088482812240535367980101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058988541493690245320067 15088482812240535367980101)
          ·
            refine ⟨2829090527295100381496269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15088482812240535367980101 2829090527295100381496269)
            ·
              refine ⟨1060908947735662643061101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2829090527295100381496269 1060908947735662643061101)
              ·
                refine ⟨397840855400873491147913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060908947735662643061101 397840855400873491147913)
                ·
                  refine ⟨298380641550655118360935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397840855400873491147913 298380641550655118360935)
                  ·
                    rfl

theorem cell20_653731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2].length) (baseStart_653731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653731 prefixEnd_653731 := by exact prefixLift 653731
  have htrace : WordTrace (prefixWord ++ tailWord_653731) baseStart_653731 baseEnd_653731 := by
    simpa [prefixWord, tailWord_653731, baseEnd_653731] using wordTrace_append hprefix tailTrace_653731
  have hstable : (prefixWord ++ tailWord_653731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653731).length < 2 ^ (prefixWord ++ tailWord_653731).sum := by decide
  have hdescent : baseEnd_653731 < baseStart_653731 := by decide
  rcases family_descends (prefixWord ++ tailWord_653731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653797 : List Nat := [1, 3, 1, 5, 2, 8]
def baseStart_653797 : Nat := 118140960795 + 653797 * 2 ^ 59
def prefixEnd_653797 : Nat := 4983230072969 + 3 ^ 40 * 653797 * 2
def baseEnd_653797 : Nat := 11052250583298230450395

theorem tailTrace_653797 : CollatzResearch.WordTrace tailWord_653797 prefixEnd_653797 11052250583298230450395 := by
  unfold tailWord_653797
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845935612412603483031645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897290408275068988687763 23845935612412603483031645)
  ·
    refine ⟨8942225854654726306136867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23845935612412603483031645 8942225854654726306136867)
    ·
      refine ⟨13413338781982089459205301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942225854654726306136867 13413338781982089459205301)
      ·
        refine ⟨1257500510810820886800497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13413338781982089459205301 1257500510810820886800497)
        ·
          refine ⟨943125383108115665100373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257500510810820886800497 943125383108115665100373)
          ·
            refine ⟨11052250583298230450395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 943125383108115665100373 11052250583298230450395)
            ·
              rfl

theorem cell20_653797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_653797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653797 prefixEnd_653797 := by exact prefixLift 653797
  have htrace : WordTrace (prefixWord ++ tailWord_653797) baseStart_653797 baseEnd_653797 := by
    simpa [prefixWord, tailWord_653797, baseEnd_653797] using wordTrace_append hprefix tailTrace_653797
  have hstable : (prefixWord ++ tailWord_653797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653797).length < 2 ^ (prefixWord ++ tailWord_653797).sum := by decide
  have hdescent : baseEnd_653797 < baseStart_653797 := by decide
  rcases family_descends (prefixWord ++ tailWord_653797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653811 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_653811 : Nat := 118140960795 + 653811 * 2 ^ 59
def prefixEnd_653811 : Nat := 4983230072969 + 3 ^ 40 * 653811 * 2
def baseEnd_653811 : Nat := 298417155730530395693941

theorem tailTrace_653811 : CollatzResearch.WordTrace tailWord_653811 prefixEnd_653811 298417155730530395693941 := by
  unfold tailWord_653811
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846446234361883874041287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897630822907922582694191 23846446234361883874041287)
  ·
    refine ⟨35769669351542825811061931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846446234361883874041287 35769669351542825811061931)
    ·
      refine ⟨53654504027314238716592897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35769669351542825811061931 53654504027314238716592897)
      ·
        refine ⟨40240878020485679037444673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53654504027314238716592897 40240878020485679037444673)
        ·
          refine ⟨30180658515364259278083505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40240878020485679037444673 30180658515364259278083505)
          ·
            refine ⟨22635493886523194458562629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30180658515364259278083505 22635493886523194458562629)
            ·
              refine ⟨4244155103723098960980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22635493886523194458562629 4244155103723098960980493)
              ·
                refine ⟨1591558163896162110367685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4244155103723098960980493 1591558163896162110367685)
                ·
                  refine ⟨298417155730530395693941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591558163896162110367685 298417155730530395693941)
                  ·
                    rfl

theorem cell20_653811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_653811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653811 prefixEnd_653811 := by exact prefixLift 653811
  have htrace : WordTrace (prefixWord ++ tailWord_653811) baseStart_653811 baseEnd_653811 := by
    simpa [prefixWord, tailWord_653811, baseEnd_653811] using wordTrace_append hprefix tailTrace_653811
  have hstable : (prefixWord ++ tailWord_653811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653811).length < 2 ^ (prefixWord ++ tailWord_653811).sum := by decide
  have hdescent : baseEnd_653811 < baseStart_653811 := by decide
  rcases family_descends (prefixWord ++ tailWord_653811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653818 : List Nat := [3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_653818 : Nat := 118140960795 + 653818 * 2 ^ 59
def prefixEnd_653818 : Nat := 4983230072969 + 3 ^ 40 * 653818 * 2
def baseEnd_653818 : Nat := 99473450240423160820193

theorem tailTrace_653818 : CollatzResearch.WordTrace tailWord_653818 prefixEnd_653818 99473450240423160820193 := by
  unfold tailWord_653818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961675386334131017386527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15897801030224349379697405 5961675386334131017386527)
  ·
    refine ⟨8942513079501196526079791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5961675386334131017386527 8942513079501196526079791)
    ·
      refine ⟨13413769619251794789119687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942513079501196526079791 13413769619251794789119687)
      ·
        refine ⟨20120654428877692183679531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13413769619251794789119687 20120654428877692183679531)
        ·
          refine ⟨30180981643316538275519297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20120654428877692183679531 30180981643316538275519297)
          ·
            refine ⟨22635736232487403706639473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30180981643316538275519297 22635736232487403706639473)
            ·
              refine ⟨16976802174365552779979605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22635736232487403706639473 16976802174365552779979605)
              ·
                refine ⟨99473450240423160820193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16976802174365552779979605 99473450240423160820193)
                ·
                  rfl

theorem cell20_653818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_653818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653818 prefixEnd_653818 := by exact prefixLift 653818
  have htrace : WordTrace (prefixWord ++ tailWord_653818) baseStart_653818 baseEnd_653818 := by
    simpa [prefixWord, tailWord_653818, baseEnd_653818] using wordTrace_append hprefix tailTrace_653818
  have hstable : (prefixWord ++ tailWord_653818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653818).length < 2 ^ (prefixWord ++ tailWord_653818).sum := by decide
  have hdescent : baseEnd_653818 < baseStart_653818 := by decide
  rcases family_descends (prefixWord ++ tailWord_653818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653828 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_653828 : Nat := 118140960795 + 653828 * 2 ^ 59
def prefixEnd_653828 : Nat := 4983230072969 + 3 ^ 40 * 653828 * 2
def baseEnd_653828 : Nat := 298424914993753892127205

theorem tailTrace_653828 : CollatzResearch.WordTrace tailWord_653828 prefixEnd_653828 298424914993753892127205 := by
  unfold tailWord_653828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923533137650147888705069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15898044183533530518273425 11923533137650147888705069)
  ·
    refine ⟨4471324926618805458264401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11923533137650147888705069 4471324926618805458264401)
    ·
      refine ⟨3353493694964104093698301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4471324926618805458264401 3353493694964104093698301)
      ·
        refine ⟨1257560135611539035136863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3353493694964104093698301 1257560135611539035136863)
        ·
          refine ⟨1886340203417308552705295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257560135611539035136863 1886340203417308552705295)
          ·
            refine ⟨2829510305125962829057943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886340203417308552705295 2829510305125962829057943)
            ·
              refine ⟨4244265457688944243586915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829510305125962829057943 4244265457688944243586915)
              ·
                refine ⟨6366398186533416365380373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244265457688944243586915 6366398186533416365380373)
                ·
                  refine ⟨298424914993753892127205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6366398186533416365380373 298424914993753892127205)
                  ·
                    rfl

theorem cell20_653828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_653828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653828 prefixEnd_653828 := by exact prefixLift 653828
  have htrace : WordTrace (prefixWord ++ tailWord_653828) baseStart_653828 baseEnd_653828 := by
    simpa [prefixWord, tailWord_653828, baseEnd_653828] using wordTrace_append hprefix tailTrace_653828
  have hstable : (prefixWord ++ tailWord_653828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653828).length < 2 ^ (prefixWord ++ tailWord_653828).sum := by decide
  have hdescent : baseEnd_653828 < baseStart_653828 := by decide
  rcases family_descends (prefixWord ++ tailWord_653828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653845 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 2]
def baseStart_653845 : Nat := 118140960795 + 653845 * 2 ^ 59
def prefixEnd_653845 : Nat := 4983230072969 + 3 ^ 40 * 653845 * 2
def baseEnd_653845 : Nat := 298432674256977388560469

theorem tailTrace_653845 : CollatzResearch.WordTrace tailWord_653845 prefixEnd_653845 298432674256977388560469 := by
  unfold tailWord_653845
  simp only [CollatzResearch.WordTrace]
  refine ⟨23847686316238707680778989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15898457544159138453852659 23847686316238707680778989)
  ·
    refine ⟨8942882368589515380292121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23847686316238707680778989 8942882368589515380292121)
    ·
      refine ⟨6707161776442136535219091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8942882368589515380292121 6707161776442136535219091)
      ·
        refine ⟨10060742664663204802828637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707161776442136535219091 10060742664663204802828637)
        ·
          refine ⟨3772778499248701801060739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10060742664663204802828637 3772778499248701801060739)
          ·
            refine ⟨5659167748873052701591109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772778499248701801060739 5659167748873052701591109)
            ·
              refine ⟨1061093952913697381548333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5659167748873052701591109 1061093952913697381548333)
              ·
                refine ⟨397910232342636518080625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061093952913697381548333 397910232342636518080625)
                ·
                  refine ⟨298432674256977388560469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397910232342636518080625 298432674256977388560469)
                  ·
                    rfl

theorem cell20_653845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_653845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653845 prefixEnd_653845 := by exact prefixLift 653845
  have htrace : WordTrace (prefixWord ++ tailWord_653845) baseStart_653845 baseEnd_653845 := by
    simpa [prefixWord, tailWord_653845, baseEnd_653845] using wordTrace_append hprefix tailTrace_653845
  have hstable : (prefixWord ++ tailWord_653845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653845).length < 2 ^ (prefixWord ++ tailWord_653845).sum := by decide
  have hdescent : baseEnd_653845 < baseStart_653845 := by decide
  rcases family_descends (prefixWord ++ tailWord_653845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653859 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_653859 : Nat := 118140960795 + 653859 * 2 ^ 59
def prefixEnd_653859 : Nat := 4983230072969 + 3 ^ 40 * 653859 * 2
def baseEnd_653859 : Nat := 298439064238455562093745

theorem tailTrace_653859 : CollatzResearch.WordTrace tailWord_653859 prefixEnd_653859 298439064238455562093745 := by
  unfold tailWord_653859
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848196938187988071788631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15898797958791992047859087 23848196938187988071788631)
  ·
    refine ⟨35772295407281982107682947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23848196938187988071788631 35772295407281982107682947)
    ·
      refine ⟨53658443110922973161524421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35772295407281982107682947 53658443110922973161524421)
      ·
        refine ⟨10060958083298057467785829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53658443110922973161524421 10060958083298057467785829)
        ·
          refine ⟨1886429640618385775209843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10060958083298057467785829 1886429640618385775209843)
          ·
            refine ⟨2829644460927578662814765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886429640618385775209843 2829644460927578662814765)
            ·
              refine ⟨1061116672847841998555537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2829644460927578662814765 1061116672847841998555537)
              ·
                refine ⟨795837504635881498916653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061116672847841998555537 795837504635881498916653)
                ·
                  refine ⟨298439064238455562093745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795837504635881498916653 298439064238455562093745)
                  ·
                    rfl

theorem cell20_653859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_653859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653859 prefixEnd_653859 := by exact prefixLift 653859
  have htrace : WordTrace (prefixWord ++ tailWord_653859) baseStart_653859 baseEnd_653859 := by
    simpa [prefixWord, tailWord_653859, baseEnd_653859] using wordTrace_append hprefix tailTrace_653859
  have hstable : (prefixWord ++ tailWord_653859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653859).length < 2 ^ (prefixWord ++ tailWord_653859).sum := by decide
  have hdescent : baseEnd_653859 < baseStart_653859 := by decide
  rcases family_descends (prefixWord ++ tailWord_653859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653866 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_653866 : Nat := 118140960795 + 653866 * 2 ^ 59
def prefixEnd_653866 : Nat := 4983230072969 + 3 ^ 40 * 653866 * 2
def baseEnd_653866 : Nat := 298442259229194648860383

theorem tailTrace_653866 : CollatzResearch.WordTrace tailWord_653866 prefixEnd_653866 298442259229194648860383 := by
  unfold tailWord_653866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962113062290657066823363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15898968166108418844862301 5962113062290657066823363)
  ·
    refine ⟨8943169593435985600235045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962113062290657066823363 8943169593435985600235045)
    ·
      refine ⟨1676844298769247300044071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8943169593435985600235045 1676844298769247300044071)
      ·
        refine ⟨2515266448153870950066107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676844298769247300044071 2515266448153870950066107)
        ·
          refine ⟨3772899672230806425099161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515266448153870950066107 3772899672230806425099161)
          ·
            refine ⟨2829674754173104818824371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772899672230806425099161 2829674754173104818824371)
            ·
              refine ⟨4244512131259657228236557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829674754173104818824371 4244512131259657228236557)
              ·
                refine ⟨1591692049222371460588709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4244512131259657228236557 1591692049222371460588709)
                ·
                  refine ⟨298442259229194648860383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591692049222371460588709 298442259229194648860383)
                  ·
                    rfl

theorem cell20_653866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_653866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653866 prefixEnd_653866 := by exact prefixLift 653866
  have htrace : WordTrace (prefixWord ++ tailWord_653866) baseStart_653866 baseEnd_653866 := by
    simpa [prefixWord, tailWord_653866, baseEnd_653866] using wordTrace_append hprefix tailTrace_653866
  have hstable : (prefixWord ++ tailWord_653866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653866).length < 2 ^ (prefixWord ++ tailWord_653866).sum := by decide
  have hdescent : baseEnd_653866 < baseStart_653866 := by decide
  rcases family_descends (prefixWord ++ tailWord_653866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653886 : List Nat := [4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_653886 : Nat := 118140960795 + 653886 * 2 ^ 59
def prefixEnd_653886 : Nat := 4983230072969 + 3 ^ 40 * 653886 * 2
def baseEnd_653886 : Nat := 99483795924721156064545

theorem tailTrace_653886 : CollatzResearch.WordTrace tailWord_653886 prefixEnd_653886 99483795924721156064545 := by
  unfold tailWord_653886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981147713636271460377689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15899454472726781122014341 2981147713636271460377689)
  ·
    refine ⟨2235860785227203595283267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2981147713636271460377689 2235860785227203595283267)
    ·
      refine ⟨3353791177840805392924901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235860785227203595283267 3353791177840805392924901)
      ·
        refine ⟨628835845845151011173419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3353791177840805392924901 628835845845151011173419)
        ·
          refine ⟨943253768767726516760129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628835845845151011173419 943253768767726516760129)
          ·
            refine ⟨707440326575794887570097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943253768767726516760129 707440326575794887570097)
            ·
              refine ⟨530580244931846165677573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707440326575794887570097 530580244931846165677573)
              ·
                refine ⟨99483795924721156064545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530580244931846165677573 99483795924721156064545)
                ·
                  rfl

theorem cell20_653886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_653886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653886 prefixEnd_653886 := by exact prefixLift 653886
  have htrace : WordTrace (prefixWord ++ tailWord_653886) baseStart_653886 baseEnd_653886 := by
    simpa [prefixWord, tailWord_653886, baseEnd_653886] using wordTrace_append hprefix tailTrace_653886
  have hstable : (prefixWord ++ tailWord_653886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653886).length < 2 ^ (prefixWord ++ tailWord_653886).sum := by decide
  have hdescent : baseEnd_653886 < baseStart_653886 := by decide
  rcases family_descends (prefixWord ++ tailWord_653886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653887 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_653887 : Nat := 118140960795 + 653887 * 2 ^ 59
def prefixEnd_653887 : Nat := 4983230072969 + 3 ^ 40 * 653887 * 2
def baseEnd_653887 : Nat := 298451844201411909160297

theorem tailTrace_653887 : CollatzResearch.WordTrace tailWord_653887 prefixEnd_653887 298451844201411909160297 := by
  unfold tailWord_653887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849218182086548853807915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15899478788057699235871943 23849218182086548853807915)
  ·
    refine ⟨35773827273129823280711873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23849218182086548853807915 35773827273129823280711873)
    ·
      refine ⟨26830370454847367460533905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35773827273129823280711873 26830370454847367460533905)
      ·
        refine ⟨20122777841135525595400429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26830370454847367460533905 20122777841135525595400429)
        ·
          refine ⟨7546041690425822098275161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20122777841135525595400429 7546041690425822098275161)
          ·
            refine ⟨5659531267819366573706371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546041690425822098275161 5659531267819366573706371)
            ·
              refine ⟨8489296901729049860559557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659531267819366573706371 8489296901729049860559557)
              ·
                refine ⟨1591743169074196848854917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8489296901729049860559557 1591743169074196848854917)
                ·
                  refine ⟨298451844201411909160297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591743169074196848854917 298451844201411909160297)
                  ·
                    rfl

theorem cell20_653887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_653887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653887 prefixEnd_653887 := by exact prefixLift 653887
  have htrace : WordTrace (prefixWord ++ tailWord_653887) baseStart_653887 baseEnd_653887 := by
    simpa [prefixWord, tailWord_653887, baseEnd_653887] using wordTrace_append hprefix tailTrace_653887
  have hstable : (prefixWord ++ tailWord_653887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653887).length < 2 ^ (prefixWord ++ tailWord_653887).sum := by decide
  have hdescent : baseEnd_653887 < baseStart_653887 := by decide
  rcases family_descends (prefixWord ++ tailWord_653887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653904 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_653904 : Nat := 118140960795 + 653904 * 2 ^ 59
def prefixEnd_653904 : Nat := 4983230072969 + 3 ^ 40 * 653904 * 2
def baseEnd_653904 : Nat := 298459603464635405593561

theorem tailTrace_653904 : CollatzResearch.WordTrace tailWord_653904 prefixEnd_653904 298459603464635405593561 := by
  unfold tailWord_653904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924919111512480378588383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15899892148683307171451177 11924919111512480378588383)
  ·
    refine ⟨17887378667268720567882575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11924919111512480378588383 17887378667268720567882575)
    ·
      refine ⟨26831068000903080851823863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17887378667268720567882575 26831068000903080851823863)
      ·
        refine ⟨40246602001354621277735795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26831068000903080851823863 40246602001354621277735795)
        ·
          refine ⟨60369903002031931916603693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40246602001354621277735795 60369903002031931916603693)
          ·
            refine ⟨22638713625761974468726385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60369903002031931916603693 22638713625761974468726385)
            ·
              refine ⟨16979035219321480851544789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22638713625761974468726385 16979035219321480851544789)
              ·
                refine ⟨397946137952847207458081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16979035219321480851544789 397946137952847207458081)
                ·
                  refine ⟨298459603464635405593561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397946137952847207458081 298459603464635405593561)
                  ·
                    rfl

theorem cell20_653904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_653904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653904 prefixEnd_653904 := by exact prefixLift 653904
  have htrace : WordTrace (prefixWord ++ tailWord_653904) baseStart_653904 baseEnd_653904 := by
    simpa [prefixWord, tailWord_653904, baseEnd_653904] using wordTrace_append hprefix tailTrace_653904
  have hstable : (prefixWord ++ tailWord_653904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653904).length < 2 ^ (prefixWord ++ tailWord_653904).sum := by decide
  have hdescent : baseEnd_653904 < baseStart_653904 := by decide
  rcases family_descends (prefixWord ++ tailWord_653904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653928 : List Nat := [2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_653928 : Nat := 118140960795 + 653928 * 2 ^ 59
def prefixEnd_653928 : Nat := 4983230072969 + 3 ^ 40 * 653928 * 2
def baseEnd_653928 : Nat := 99490185906199329597821

theorem tailTrace_653928 : CollatzResearch.WordTrace tailWord_653928 prefixEnd_653928 99490185906199329597821 := by
  unfold tailWord_653928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925356787469006428025219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15900475716625341904033625 11925356787469006428025219)
  ·
    refine ⟨17888035181203509642037829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11925356787469006428025219 17888035181203509642037829)
    ·
      refine ⟨3354006596475658057882093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17888035181203509642037829 3354006596475658057882093)
      ·
        refine ⟨1257752473678371771705785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3354006596475658057882093 1257752473678371771705785)
        ·
          refine ⟨943314355258778828779339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257752473678371771705785 943314355258778828779339)
          ·
            refine ⟨1414971532888168243169009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943314355258778828779339 1414971532888168243169009)
            ·
              refine ⟨1061228649666126182376757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414971532888168243169009 1061228649666126182376757)
              ·
                refine ⟨99490185906199329597821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061228649666126182376757 99490185906199329597821)
                ·
                  rfl

theorem cell20_653928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_653928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653928 prefixEnd_653928 := by exact prefixLift 653928
  have htrace : WordTrace (prefixWord ++ tailWord_653928) baseStart_653928 baseEnd_653928 := by
    simpa [prefixWord, tailWord_653928, baseEnd_653928] using wordTrace_append hprefix tailTrace_653928
  have hstable : (prefixWord ++ tailWord_653928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653928).length < 2 ^ (prefixWord ++ tailWord_653928).sum := by decide
  have hdescent : baseEnd_653928 < baseStart_653928 := by decide
  rcases family_descends (prefixWord ++ tailWord_653928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653932 : List Nat := [2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_653932 : Nat := 118140960795 + 653932 * 2 ^ 59
def prefixEnd_653932 : Nat := 4983230072969 + 3 ^ 40 * 653932 * 2
def baseEnd_653932 : Nat := 99490794475863917553371

theorem tailTrace_653932 : CollatzResearch.WordTrace tailWord_653932 prefixEnd_653932 99490794475863917553371 := by
  unfold tailWord_653932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925429733461760769598025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15900572977949014359464033 11925429733461760769598025)
  ·
    refine ⟨8944072300096320577198519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11925429733461760769598025 8944072300096320577198519)
    ·
      refine ⟨13416108450144480865797779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944072300096320577198519 13416108450144480865797779)
      ·
        refine ⟨20124162675216721298696669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13416108450144480865797779 20124162675216721298696669)
        ·
          refine ⟨7546561003206270487011251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20124162675216721298696669 7546561003206270487011251)
          ·
            refine ⟨11319841504809405730516877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546561003206270487011251 11319841504809405730516877)
            ·
              refine ⟨4244940564303527148943829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11319841504809405730516877 4244940564303527148943829)
              ·
                refine ⟨99490794475863917553371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4244940564303527148943829 99490794475863917553371)
                ·
                  rfl

theorem cell20_653932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_653932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653932 prefixEnd_653932 := by exact prefixLift 653932
  have htrace : WordTrace (prefixWord ++ tailWord_653932) baseStart_653932 baseEnd_653932 := by
    simpa [prefixWord, tailWord_653932, baseEnd_653932] using wordTrace_append hprefix tailTrace_653932
  have hstable : (prefixWord ++ tailWord_653932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653932).length < 2 ^ (prefixWord ++ tailWord_653932).sum := by decide
  have hdescent : baseEnd_653932 < baseStart_653932 := by decide
  rcases family_descends (prefixWord ++ tailWord_653932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653935 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_653935 : Nat := 118140960795 + 653935 * 2 ^ 59
def prefixEnd_653935 : Nat := 4983230072969 + 3 ^ 40 * 653935 * 2
def baseEnd_653935 : Nat := 298473752709337075560101

theorem tailTrace_653935 : CollatzResearch.WordTrace tailWord_653935 prefixEnd_653935 298473752709337075560101 := by
  unfold tailWord_653935
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850968885912653051555259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15900645923941768701036839 23850968885912653051555259)
  ·
    refine ⟨35776453328868979577332889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23850968885912653051555259 35776453328868979577332889)
    ·
      refine ⟨26832339996651734682999667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35776453328868979577332889 26832339996651734682999667)
      ·
        refine ⟨40248509994977602024499501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26832339996651734682999667 40248509994977602024499501)
        ·
          refine ⟨15093191248116600759187313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40248509994977602024499501 15093191248116600759187313)
          ·
            refine ⟨11319893436087450569390485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15093191248116600759187313 11319893436087450569390485)
            ·
              refine ⟨530620004816599245440179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11319893436087450569390485 530620004816599245440179)
              ·
                refine ⟨795930007224898868160269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530620004816599245440179 795930007224898868160269)
                ·
                  refine ⟨298473752709337075560101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795930007224898868160269 298473752709337075560101)
                  ·
                    rfl

theorem cell20_653935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_653935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653935 prefixEnd_653935 := by exact prefixLift 653935
  have htrace : WordTrace (prefixWord ++ tailWord_653935) baseStart_653935 baseEnd_653935 := by
    simpa [prefixWord, tailWord_653935, baseEnd_653935] using wordTrace_append hprefix tailTrace_653935
  have hstable : (prefixWord ++ tailWord_653935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653935).length < 2 ^ (prefixWord ++ tailWord_653935).sum := by decide
  have hdescent : baseEnd_653935 < baseStart_653935 := by decide
  rcases family_descends (prefixWord ++ tailWord_653935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653939 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_653939 : Nat := 118140960795 + 653939 * 2 ^ 59
def prefixEnd_653939 : Nat := 4983230072969 + 3 ^ 40 * 653939 * 2
def baseEnd_653939 : Nat := 298475578418330839426751

theorem tailTrace_653939 : CollatzResearch.WordTrace tailWord_653939 prefixEnd_653939 298475578418330839426751 := by
  unfold tailWord_653939
  simp only [CollatzResearch.WordTrace]
  refine ⟨23851114777898161734700871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15900743185265441156467247 23851114777898161734700871)
  ·
    refine ⟨35776672166847242602051307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23851114777898161734700871 35776672166847242602051307)
    ·
      refine ⟨53665008250270863903076961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35776672166847242602051307 53665008250270863903076961)
      ·
        refine ⟨40248756187703147927307721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53665008250270863903076961 40248756187703147927307721)
        ·
          refine ⟨30186567140777360945480791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40248756187703147927307721 30186567140777360945480791)
          ·
            refine ⟨45279850711166041418221187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30186567140777360945480791 45279850711166041418221187)
            ·
              refine ⟨67919776066749062127331781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45279850711166041418221187 67919776066749062127331781)
              ·
                refine ⟨12734958012515449148874709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67919776066749062127331781 12734958012515449148874709)
                ·
                  refine ⟨298475578418330839426751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12734958012515449148874709 298475578418330839426751)
                  ·
                    rfl

theorem cell20_653939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_653939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_653939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_653939 prefixEnd_653939 := by exact prefixLift 653939
  have htrace : WordTrace (prefixWord ++ tailWord_653939) baseStart_653939 baseEnd_653939 := by
    simpa [prefixWord, tailWord_653939, baseEnd_653939] using wordTrace_append hprefix tailTrace_653939
  have hstable : (prefixWord ++ tailWord_653939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653939).length < 2 ^ (prefixWord ++ tailWord_653939).sum := by decide
  have hdescent : baseEnd_653939 < baseStart_653939 := by decide
  rcases family_descends (prefixWord ++ tailWord_653939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654028 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_654028 : Nat := 118140960795 + 654028 * 2 ^ 59
def prefixEnd_654028 : Nat := 4983230072969 + 3 ^ 40 * 654028 * 2
def baseEnd_654028 : Nat := 298516200443442085459721

theorem tailTrace_654028 : CollatzResearch.WordTrace tailWord_654028 prefixEnd_654028 298516200443442085459721 := by
  unfold tailWord_654028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927180437287864967345369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15902907249717153289793825 11927180437287864967345369)
  ·
    refine ⟨8945385327965898725509027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11927180437287864967345369 8945385327965898725509027)
    ·
      refine ⟨13418077991948848088263541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8945385327965898725509027 13418077991948848088263541)
      ·
        refine ⟨1257944811745204508274707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13418077991948848088263541 1257944811745204508274707)
        ·
          refine ⟨1886917217617806762412061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257944811745204508274707 1886917217617806762412061)
          ·
            refine ⟨707593956606677535904523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1886917217617806762412061 707593956606677535904523)
            ·
              refine ⟨1061390934910016303856785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707593956606677535904523 1061390934910016303856785)
              ·
                refine ⟨796043201182512227892589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061390934910016303856785 796043201182512227892589)
                ·
                  refine ⟨298516200443442085459721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796043201182512227892589 298516200443442085459721)
                  ·
                    rfl

theorem cell20_654028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_654028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654028 prefixEnd_654028 := by exact prefixLift 654028
  have htrace : WordTrace (prefixWord ++ tailWord_654028) baseStart_654028 baseEnd_654028 := by
    simpa [prefixWord, tailWord_654028, baseEnd_654028] using wordTrace_append hprefix tailTrace_654028
  have hstable : (prefixWord ++ tailWord_654028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654028).length < 2 ^ (prefixWord ++ tailWord_654028).sum := by decide
  have hdescent : baseEnd_654028 < baseStart_654028 := by decide
  rcases family_descends (prefixWord ++ tailWord_654028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654039 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_654039 : Nat := 118140960795 + 654039 * 2 ^ 59
def prefixEnd_654039 : Nat := 4983230072969 + 3 ^ 40 * 654039 * 2
def baseEnd_654039 : Nat := 298521221143174936093009

theorem tailTrace_654039 : CollatzResearch.WordTrace tailWord_654039 prefixEnd_654039 298521221143174936093009 := by
  unfold tailWord_654039
  simp only [CollatzResearch.WordTrace]
  refine ⟨23854762077535878813341171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15903174718357252542227447 23854762077535878813341171)
  ·
    refine ⟨35782143116303818220011757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23854762077535878813341171 35782143116303818220011757)
    ·
      refine ⟨13418303668613931832504409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35782143116303818220011757 13418303668613931832504409)
      ·
        refine ⟨10063727751460448874378307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13418303668613931832504409 10063727751460448874378307)
        ·
          refine ⟨15095591627190673311567461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10063727751460448874378307 15095591627190673311567461)
          ·
            refine ⟨2830423430098251245918899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15095591627190673311567461 2830423430098251245918899)
            ·
              refine ⟨4245635145147376868878349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830423430098251245918899 4245635145147376868878349)
              ·
                refine ⟨1592113179430266325829381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4245635145147376868878349 1592113179430266325829381)
                ·
                  refine ⟨298521221143174936093009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592113179430266325829381 298521221143174936093009)
                  ·
                    rfl

theorem cell20_654039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_654039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654039 prefixEnd_654039 := by exact prefixLift 654039
  have htrace : WordTrace (prefixWord ++ tailWord_654039) baseStart_654039 baseEnd_654039 := by
    simpa [prefixWord, tailWord_654039, baseEnd_654039] using wordTrace_append hprefix tailTrace_654039
  have hstable : (prefixWord ++ tailWord_654039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654039).length < 2 ^ (prefixWord ++ tailWord_654039).sum := by decide
  have hdescent : baseEnd_654039 < baseStart_654039 := by decide
  rcases family_descends (prefixWord ++ tailWord_654039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654063 : List Nat := [1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_654063 : Nat := 118140960795 + 654063 * 2 ^ 59
def prefixEnd_654063 : Nat := 4983230072969 + 3 ^ 40 * 654063 * 2
def baseEnd_654063 : Nat := 99510725132379173097637

theorem tailTrace_654063 : CollatzResearch.WordTrace tailWord_654063 prefixEnd_654063 99510725132379173097637 := by
  unfold tailWord_654063
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855637429448930912214843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15903758286299287274809895 23855637429448930912214843)
  ·
    refine ⟨35783456144173396368322265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23855637429448930912214843 35783456144173396368322265)
    ·
      refine ⟨26837592108130047276241699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35783456144173396368322265 26837592108130047276241699)
      ·
        refine ⟨40256388162195070914362549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26837592108130047276241699 40256388162195070914362549)
        ·
          refine ⟨3774036390205787898221489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40256388162195070914362549 3774036390205787898221489)
          ·
            refine ⟨2830527292654340923666117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774036390205787898221489 2830527292654340923666117)
            ·
              refine ⟨530723867372688923187397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2830527292654340923666117 530723867372688923187397)
              ·
                refine ⟨99510725132379173097637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530723867372688923187397 99510725132379173097637)
                ·
                  rfl

theorem cell20_654063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_654063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654063 prefixEnd_654063 := by exact prefixLift 654063
  have htrace : WordTrace (prefixWord ++ tailWord_654063) baseStart_654063 baseEnd_654063 := by
    simpa [prefixWord, tailWord_654063, baseEnd_654063] using wordTrace_append hprefix tailTrace_654063
  have hstable : (prefixWord ++ tailWord_654063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654063).length < 2 ^ (prefixWord ++ tailWord_654063).sum := by decide
  have hdescent : baseEnd_654063 < baseStart_654063 := by decide
  rcases family_descends (prefixWord ++ tailWord_654063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654070 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_654070 : Nat := 118140960795 + 654070 * 2 ^ 59
def prefixEnd_654070 : Nat := 4983230072969 + 3 ^ 40 * 654070 * 2
def baseEnd_654070 : Nat := 298535370387876606059549

theorem tailTrace_654070 : CollatzResearch.WordTrace tailWord_654070 prefixEnd_654070 298535370387876606059549 := by
  unfold tailWord_654070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490993296276473194232479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15903928493615714071813109 1490993296276473194232479)
  ·
    refine ⟨2236489944414709791348719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490993296276473194232479 2236489944414709791348719)
    ·
      refine ⟨3354734916622064687023079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236489944414709791348719 3354734916622064687023079)
      ·
        refine ⟨5032102374933097030534619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354734916622064687023079 5032102374933097030534619)
        ·
          refine ⟨7548153562399645545801929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032102374933097030534619 7548153562399645545801929)
          ·
            refine ⟨5661115171799734159351447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548153562399645545801929 5661115171799734159351447)
            ·
              refine ⟨8491672757699601239027171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661115171799734159351447 8491672757699601239027171)
              ·
                refine ⟨12737509136549401858540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491672757699601239027171 12737509136549401858540757)
                ·
                  refine ⟨298535370387876606059549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12737509136549401858540757 298535370387876606059549)
                  ·
                    rfl

theorem cell20_654070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_654070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654070 prefixEnd_654070 := by exact prefixLift 654070
  have htrace : WordTrace (prefixWord ++ tailWord_654070) baseStart_654070 baseEnd_654070 := by
    simpa [prefixWord, tailWord_654070, baseEnd_654070] using wordTrace_append hprefix tailTrace_654070
  have hstable : (prefixWord ++ tailWord_654070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654070).length < 2 ^ (prefixWord ++ tailWord_654070).sum := by decide
  have hdescent : baseEnd_654070 < baseStart_654070 := by decide
  rcases family_descends (prefixWord ++ tailWord_654070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654142 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_654142 : Nat := 118140960795 + 654142 * 2 ^ 59
def prefixEnd_654142 : Nat := 4983230072969 + 3 ^ 40 * 654142 * 2
def baseEnd_654142 : Nat := 298568233149764355659255

theorem tailTrace_654142 : CollatzResearch.WordTrace tailWord_654142 prefixEnd_654142 298568233149764355659255 := by
  unfold tailWord_654142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982314849520340925542585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15905679197441818269560453 2982314849520340925542585)
  ·
    refine ⟨2236736137140255694156939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2982314849520340925542585 2236736137140255694156939)
    ·
      refine ⟨3355104205710383541235409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236736137140255694156939 3355104205710383541235409)
      ·
        refine ⟨2516328154282787655926557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3355104205710383541235409 2516328154282787655926557)
        ·
          refine ⟨943623057856045370972459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2516328154282787655926557 943623057856045370972459)
          ·
            refine ⟨1415434586784068056458689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943623057856045370972459 1415434586784068056458689)
            ·
              refine ⟨1061575940088051042344017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415434586784068056458689 1061575940088051042344017)
              ·
                refine ⟨796181955066038281758013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061575940088051042344017 796181955066038281758013)
                ·
                  refine ⟨298568233149764355659255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796181955066038281758013 298568233149764355659255)
                  ·
                    rfl

theorem cell20_654142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_654142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654142 prefixEnd_654142 := by exact prefixLift 654142
  have htrace : WordTrace (prefixWord ++ tailWord_654142) baseStart_654142 baseEnd_654142 := by
    simpa [prefixWord, tailWord_654142, baseEnd_654142] using wordTrace_append hprefix tailTrace_654142
  have hstable : (prefixWord ++ tailWord_654142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654142).length < 2 ^ (prefixWord ++ tailWord_654142).sum := by decide
  have hdescent : baseEnd_654142 < baseStart_654142 := by decide
  rcases family_descends (prefixWord ++ tailWord_654142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654160 : List Nat := [2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_654160 : Nat := 118140960795 + 654160 * 2 ^ 59
def prefixEnd_654160 : Nat := 4983230072969 + 3 ^ 40 * 654160 * 2
def baseEnd_654160 : Nat := 99525482946745431019727

theorem tailTrace_654160 : CollatzResearch.WordTrace tailWord_654160 prefixEnd_654160 99525482946745431019727 := by
  unfold tailWord_654160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929587655048758239247967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15906116873398344318997289 11929587655048758239247967)
  ·
    refine ⟨17894381482573137358871951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11929587655048758239247967 17894381482573137358871951)
    ·
      refine ⟨26841572223859706038307927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17894381482573137358871951 26841572223859706038307927)
      ·
        refine ⟨40262358335789559057461891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26841572223859706038307927 40262358335789559057461891)
        ·
          refine ⟨60393537503684338586192837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40262358335789559057461891 60393537503684338586192837)
          ·
            refine ⟨11323788281940813484911157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60393537503684338586192837 11323788281940813484911157)
            ·
              refine ⟨1061605151431951264210421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11323788281940813484911157 1061605151431951264210421)
              ·
                refine ⟨99525482946745431019727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061605151431951264210421 99525482946745431019727)
                ·
                  rfl

theorem cell20_654160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_654160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654160 prefixEnd_654160 := by exact prefixLift 654160
  have htrace : WordTrace (prefixWord ++ tailWord_654160) baseStart_654160 baseEnd_654160 := by
    simpa [prefixWord, tailWord_654160, baseEnd_654160] using wordTrace_append hprefix tailTrace_654160
  have hstable : (prefixWord ++ tailWord_654160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654160).length < 2 ^ (prefixWord ++ tailWord_654160).sum := by decide
  have hdescent : baseEnd_654160 < baseStart_654160 := by decide
  rcases family_descends (prefixWord ++ tailWord_654160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654201 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_654201 : Nat := 118140960795 + 654201 * 2 ^ 59
def prefixEnd_654201 : Nat := 4983230072969 + 3 ^ 40 * 654201 * 2
def baseEnd_654201 : Nat := 298595162357422372692347

theorem tailTrace_654201 : CollatzResearch.WordTrace tailWord_654201 prefixEnd_654201 298595162357422372692347 := by
  unfold tailWord_654201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860670702948980480738457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15907113801965986987158971 23860670702948980480738457)
  ·
    refine ⟨17895503027211735360553843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23860670702948980480738457 17895503027211735360553843)
    ·
      refine ⟨26843254540817603040830765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17895503027211735360553843 26843254540817603040830765)
      ·
        refine ⟨10066220452806601140311537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26843254540817603040830765 10066220452806601140311537)
        ·
          refine ⟨7549665339604950855233653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10066220452806601140311537 7549665339604950855233653)
          ·
            refine ⟨707781125587964142678155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7549665339604950855233653 707781125587964142678155)
            ·
              refine ⟨1061671688381946214017233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707781125587964142678155 1061671688381946214017233)
              ·
                refine ⟨796253766286459660512925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061671688381946214017233 796253766286459660512925)
                ·
                  refine ⟨298595162357422372692347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796253766286459660512925 298595162357422372692347)
                  ·
                    rfl

theorem cell20_654201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_654201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654201 prefixEnd_654201 := by exact prefixLift 654201
  have htrace : WordTrace (prefixWord ++ tailWord_654201) baseStart_654201 baseEnd_654201 := by
    simpa [prefixWord, tailWord_654201, baseEnd_654201] using wordTrace_append hprefix tailTrace_654201
  have hstable : (prefixWord ++ tailWord_654201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654201).length < 2 ^ (prefixWord ++ tailWord_654201).sum := by decide
  have hdescent : baseEnd_654201 < baseStart_654201 := by decide
  rcases family_descends (prefixWord ++ tailWord_654201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654218 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_654218 : Nat := 118140960795 + 654218 * 2 ^ 59
def prefixEnd_654218 : Nat := 4983230072969 + 3 ^ 40 * 654218 * 2
def baseEnd_654218 : Nat := 298602921620645869125611

theorem tailTrace_654218 : CollatzResearch.WordTrace tailWord_654218 prefixEnd_654218 298602921620645869125611 := by
  unfold tailWord_654218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965322685971848096026827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15907527162591594922738205 5965322685971848096026827)
  ·
    refine ⟨8947984028957772144040241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5965322685971848096026827 8947984028957772144040241)
    ·
      refine ⟨6710988021718329108030181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8947984028957772144040241 6710988021718329108030181)
      ·
        refine ⟨1258310254072186707755659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6710988021718329108030181 1258310254072186707755659)
        ·
          refine ⟨1887465381108280061633489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258310254072186707755659 1887465381108280061633489)
          ·
            refine ⟨1415599035831210046225117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887465381108280061633489 1415599035831210046225117)
            ·
              refine ⟨530849638436703767334419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415599035831210046225117 530849638436703767334419)
              ·
                refine ⟨796274457655055651001629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530849638436703767334419 796274457655055651001629)
                ·
                  refine ⟨298602921620645869125611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796274457655055651001629 298602921620645869125611)
                  ·
                    rfl

theorem cell20_654218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_654218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654218 prefixEnd_654218 := by exact prefixLift 654218
  have htrace : WordTrace (prefixWord ++ tailWord_654218) baseStart_654218 baseEnd_654218 := by
    simpa [prefixWord, tailWord_654218, baseEnd_654218] using wordTrace_append hprefix tailTrace_654218
  have hstable : (prefixWord ++ tailWord_654218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654218).length < 2 ^ (prefixWord ++ tailWord_654218).sum := by decide
  have hdescent : baseEnd_654218 < baseStart_654218 := by decide
  rcases family_descends (prefixWord ++ tailWord_654218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654229 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_654229 : Nat := 118140960795 + 654229 * 2 ^ 59
def prefixEnd_654229 : Nat := 4983230072969 + 3 ^ 40 * 654229 * 2
def baseEnd_654229 : Nat := 298607942320378719758899

theorem tailTrace_654229 : CollatzResearch.WordTrace tailWord_654229 prefixEnd_654229 298607942320378719758899 := by
  unfold tailWord_654229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23861691946847541262757741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15907794631231694175171827 23861691946847541262757741)
  ·
    refine ⟨8948134480067827973534153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23861691946847541262757741 8948134480067827973534153)
    ·
      refine ⟨6711100860050870980150615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8948134480067827973534153 6711100860050870980150615)
      ·
        refine ⟨10066651290076306470225923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6711100860050870980150615 10066651290076306470225923)
        ·
          refine ⟨15099976935114459705338885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10066651290076306470225923 15099976935114459705338885)
          ·
            refine ⟨2831245675333961194751041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15099976935114459705338885 2831245675333961194751041)
            ·
              refine ⟨2123434256500470896063281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831245675333961194751041 2123434256500470896063281)
              ·
                refine ⟨1592575692375353172047461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123434256500470896063281 1592575692375353172047461)
                ·
                  refine ⟨298607942320378719758899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592575692375353172047461 298607942320378719758899)
                  ·
                    rfl

theorem cell20_654229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_654229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654229 prefixEnd_654229 := by exact prefixLift 654229
  have htrace : WordTrace (prefixWord ++ tailWord_654229) baseStart_654229 baseEnd_654229 := by
    simpa [prefixWord, tailWord_654229, baseEnd_654229] using wordTrace_append hprefix tailTrace_654229
  have hstable : (prefixWord ++ tailWord_654229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654229).length < 2 ^ (prefixWord ++ tailWord_654229).sum := by decide
  have hdescent : baseEnd_654229 < baseStart_654229 := by decide
  rcases family_descends (prefixWord ++ tailWord_654229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654242 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_654242 : Nat := 118140960795 + 654242 * 2 ^ 59
def prefixEnd_654242 : Nat := 4983230072969 + 3 ^ 40 * 654242 * 2
def baseEnd_654242 : Nat := 298613875874608452325513

theorem tailTrace_654242 : CollatzResearch.WordTrace tailWord_654242 prefixEnd_654242 298613875874608452325513 := by
  unfold tailWord_654242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965541523950111120745245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15908110730533629655320653 5965541523950111120745245)
  ·
    refine ⟨2237078071481291670279467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5965541523950111120745245 2237078071481291670279467)
    ·
      refine ⟨3355617107221937505419201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237078071481291670279467 3355617107221937505419201)
      ·
        refine ⟨2516712830416453129064401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3355617107221937505419201 2516712830416453129064401)
        ·
          refine ⟨1887534622812339846798301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2516712830416453129064401 1887534622812339846798301)
          ·
            refine ⟨707825483554627442549363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1887534622812339846798301 707825483554627442549363)
            ·
              refine ⟨1061738225331941163824045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707825483554627442549363 1061738225331941163824045)
              ·
                refine ⟨398151834499477936434017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061738225331941163824045 398151834499477936434017)
                ·
                  refine ⟨298613875874608452325513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398151834499477936434017 298613875874608452325513)
                  ·
                    rfl

theorem cell20_654242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_654242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654242 prefixEnd_654242 := by exact prefixLift 654242
  have htrace : WordTrace (prefixWord ++ tailWord_654242) baseStart_654242 baseEnd_654242 := by
    simpa [prefixWord, tailWord_654242, baseEnd_654242] using wordTrace_append hprefix tailTrace_654242
  have hstable : (prefixWord ++ tailWord_654242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654242).length < 2 ^ (prefixWord ++ tailWord_654242).sum := by decide
  have hdescent : baseEnd_654242 < baseStart_654242 := by decide
  rcases family_descends (prefixWord ++ tailWord_654242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654243 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_654243 : Nat := 118140960795 + 654243 * 2 ^ 59
def prefixEnd_654243 : Nat := 4983230072969 + 3 ^ 40 * 654243 * 2
def baseEnd_654243 : Nat := 298614332301856893292175

theorem tailTrace_654243 : CollatzResearch.WordTrace tailWord_654243 prefixEnd_654243 298614332301856893292175 := by
  unfold tailWord_654243
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862202568796821653767383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15908135045864547769178255 23862202568796821653767383)
  ·
    refine ⟨35793303853195232480651075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23862202568796821653767383 35793303853195232480651075)
    ·
      refine ⟨53689955779792848720976613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35793303853195232480651075 53689955779792848720976613)
      ·
        refine ⟨10066866708711159135183115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53689955779792848720976613 10066866708711159135183115)
        ·
          refine ⟨15100300063066738702774673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10066866708711159135183115 15100300063066738702774673)
          ·
            refine ⟨11325225047300054027081005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15100300063066738702774673 11325225047300054027081005)
            ·
              refine ⟨4246959392737520260155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11325225047300054027081005 4246959392737520260155377)
              ·
                refine ⟨3185219544553140195116533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246959392737520260155377 3185219544553140195116533)
                ·
                  refine ⟨298614332301856893292175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3185219544553140195116533 298614332301856893292175)
                  ·
                    rfl

theorem cell20_654243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_654243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654243 prefixEnd_654243 := by exact prefixLift 654243
  have htrace : WordTrace (prefixWord ++ tailWord_654243) baseStart_654243 baseEnd_654243 := by
    simpa [prefixWord, tailWord_654243, baseEnd_654243] using wordTrace_append hprefix tailTrace_654243
  have hstable : (prefixWord ++ tailWord_654243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654243).length < 2 ^ (prefixWord ++ tailWord_654243).sum := by decide
  have hdescent : baseEnd_654243 < baseStart_654243 := by decide
  rcases family_descends (prefixWord ++ tailWord_654243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654288 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_654288 : Nat := 118140960795 + 654288 * 2 ^ 59
def prefixEnd_654288 : Nat := 4983230072969 + 3 ^ 40 * 654288 * 2
def baseEnd_654288 : Nat := 298634871528036736791991

theorem tailTrace_654288 : CollatzResearch.WordTrace tailWord_654288 prefixEnd_654288 298634871528036736791991 := by
  unfold tailWord_654288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931921926816897169577759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15909229235755862892770345 11931921926816897169577759)
  ·
    refine ⟨17897882890225345754366639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931921926816897169577759 17897882890225345754366639)
    ·
      refine ⟨26846824335338018631549959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897882890225345754366639 26846824335338018631549959)
      ·
        refine ⟨40270236503007027947324939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846824335338018631549959 40270236503007027947324939)
        ·
          refine ⟨60405354754510541920987409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40270236503007027947324939 60405354754510541920987409)
          ·
            refine ⟨45304016065882906440740557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60405354754510541920987409 45304016065882906440740557)
            ·
              refine ⟨16989006024706089915277709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45304016065882906440740557 16989006024706089915277709)
              ·
                refine ⟨6370877259264783718229141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16989006024706089915277709 6370877259264783718229141)
                ·
                  refine ⟨298634871528036736791991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6370877259264783718229141 298634871528036736791991)
                  ·
                    rfl

theorem cell20_654288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_654288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654288 prefixEnd_654288 := by exact prefixLift 654288
  have htrace : WordTrace (prefixWord ++ tailWord_654288) baseStart_654288 baseEnd_654288 := by
    simpa [prefixWord, tailWord_654288, baseEnd_654288] using wordTrace_append hprefix tailTrace_654288
  have hstable : (prefixWord ++ tailWord_654288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654288).length < 2 ^ (prefixWord ++ tailWord_654288).sum := by decide
  have hdescent : baseEnd_654288 < baseStart_654288 := by decide
  rcases family_descends (prefixWord ++ tailWord_654288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654325 : List Nat := [1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_654325 : Nat := 118140960795 + 654325 * 2 ^ 59
def prefixEnd_654325 : Nat := 4983230072969 + 3 ^ 40 * 654325 * 2
def baseEnd_654325 : Nat := 99550586445409684186169

theorem tailTrace_654325 : CollatzResearch.WordTrace tailWord_654325 prefixEnd_654325 99550586445409684186169 := by
  unfold tailWord_654325
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865193354499749658252429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910128902999833105501619 23865193354499749658252429)
  ·
    refine ⟨8949447507937406121844661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23865193354499749658252429 8949447507937406121844661)
    ·
      refine ⟨839010703869131823922937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8949447507937406121844661 839010703869131823922937)
      ·
        refine ⟨629258027901848867942203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839010703869131823922937 629258027901848867942203)
        ·
          refine ⟨943887041852773301913305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629258027901848867942203 943887041852773301913305)
          ·
            refine ⟨707915281389579976434979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943887041852773301913305 707915281389579976434979)
            ·
              refine ⟨1061872922084369964652469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707915281389579976434979 1061872922084369964652469)
              ·
                refine ⟨99550586445409684186169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061872922084369964652469 99550586445409684186169)
                ·
                  rfl

theorem cell20_654325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_654325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654325 prefixEnd_654325 := by exact prefixLift 654325
  have htrace : WordTrace (prefixWord ++ tailWord_654325) baseStart_654325 baseEnd_654325 := by
    simpa [prefixWord, tailWord_654325, baseEnd_654325] using wordTrace_append hprefix tailTrace_654325
  have hstable : (prefixWord ++ tailWord_654325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654325).length < 2 ^ (prefixWord ++ tailWord_654325).sum := by decide
  have hdescent : baseEnd_654325 < baseStart_654325 := by decide
  rcases family_descends (prefixWord ++ tailWord_654325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654343 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_654343 : Nat := 118140960795 + 654343 * 2 ^ 59
def prefixEnd_654343 : Nat := 4983230072969 + 3 ^ 40 * 654343 * 2
def baseEnd_654343 : Nat := 298659975026700989958433

theorem tailTrace_654343 : CollatzResearch.WordTrace tailWord_654343 prefixEnd_654343 298659975026700989958433 := by
  unfold tailWord_654343
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865849868434538732407683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910566578956359154938455 23865849868434538732407683)
  ·
    refine ⟨35798774802651808098611525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23865849868434538732407683 35798774802651808098611525)
    ·
      refine ⟨6712270275497214018489661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35798774802651808098611525 6712270275497214018489661)
      ·
        refine ⟨2517101353311455256933623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6712270275497214018489661 2517101353311455256933623)
        ·
          refine ⟨3775652029967182885400435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517101353311455256933623 3775652029967182885400435)
          ·
            refine ⟨5663478044950774328100653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775652029967182885400435 5663478044950774328100653)
            ·
              refine ⟨2123804266856540373037745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5663478044950774328100653 2123804266856540373037745)
              ·
                refine ⟨1592853200142405279778309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123804266856540373037745 1592853200142405279778309)
                ·
                  refine ⟨298659975026700989958433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592853200142405279778309 298659975026700989958433)
                  ·
                    rfl

theorem cell20_654343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_654343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654343 prefixEnd_654343 := by exact prefixLift 654343
  have htrace : WordTrace (prefixWord ++ tailWord_654343) baseStart_654343 baseEnd_654343 := by
    simpa [prefixWord, tailWord_654343, baseEnd_654343] using wordTrace_append hprefix tailTrace_654343
  have hstable : (prefixWord ++ tailWord_654343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654343).length < 2 ^ (prefixWord ++ tailWord_654343).sum := by decide
  have hdescent : baseEnd_654343 < baseStart_654343 := by decide
  rcases family_descends (prefixWord ++ tailWord_654343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654360 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_654360 : Nat := 118140960795 + 654360 * 2 ^ 59
def prefixEnd_654360 : Nat := 4983230072969 + 3 ^ 40 * 654360 * 2
def baseEnd_654360 : Nat := 298667734289924486391697

theorem tailTrace_654360 : CollatzResearch.WordTrace tailWord_654360 prefixEnd_654360 298667734289924486391697 := by
  unfold tailWord_654360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933234954686475317888267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15910979939581967090517689 11933234954686475317888267)
  ·
    refine ⟨17899852432029712976832401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11933234954686475317888267 17899852432029712976832401)
    ·
      refine ⟨13424889324022284732624301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17899852432029712976832401 13424889324022284732624301)
      ·
        refine ⟨5034333496508356774734113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13424889324022284732624301 5034333496508356774734113)
        ·
          refine ⟨3775750122381267581050585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034333496508356774734113 3775750122381267581050585)
          ·
            refine ⟨2831812591785950685787939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775750122381267581050585 2831812591785950685787939)
            ·
              refine ⟨4247718887678926028681909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831812591785950685787939 4247718887678926028681909)
              ·
                refine ⟨398223645719899315188929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4247718887678926028681909 398223645719899315188929)
                ·
                  refine ⟨298667734289924486391697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398223645719899315188929 298667734289924486391697)
                  ·
                    rfl

theorem cell20_654360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_654360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654360 prefixEnd_654360 := by exact prefixLift 654360
  have htrace : WordTrace (prefixWord ++ tailWord_654360) baseStart_654360 baseEnd_654360 := by
    simpa [prefixWord, tailWord_654360, baseEnd_654360] using wordTrace_append hprefix tailTrace_654360
  have hstable : (prefixWord ++ tailWord_654360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654360).length < 2 ^ (prefixWord ++ tailWord_654360).sum := by decide
  have hdescent : baseEnd_654360 < baseStart_654360 := by decide
  rcases family_descends (prefixWord ++ tailWord_654360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654398 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_654398 : Nat := 118140960795 + 654398 * 2 ^ 59
def prefixEnd_654398 : Nat := 4983230072969 + 3 ^ 40 * 654398 * 2
def baseEnd_654398 : Nat := 298685078525365243124875

theorem tailTrace_654398 : CollatzResearch.WordTrace tailWord_654398 prefixEnd_654398 298685078525365243124875 := by
  unfold tailWord_654398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983481985404410390707481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15911903922156855417106565 2983481985404410390707481)
  ·
    refine ⟨2237611489053307793030611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2983481985404410390707481 2237611489053307793030611)
    ·
      refine ⟨3356417233579961689545917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237611489053307793030611 3356417233579961689545917)
      ·
        refine ⟨1258656462592485633579719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3356417233579961689545917 1258656462592485633579719)
        ·
          refine ⟨1887984693888728450369579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258656462592485633579719 1887984693888728450369579)
          ·
            refine ⟨2831977040833092675554369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887984693888728450369579 2831977040833092675554369)
            ·
              refine ⟨2123982780624819506665777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831977040833092675554369 2123982780624819506665777)
              ·
                refine ⟨1592987085468614629999333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123982780624819506665777 1592987085468614629999333)
                ·
                  refine ⟨298685078525365243124875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592987085468614629999333 298685078525365243124875)
                  ·
                    rfl

theorem cell20_654398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_654398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654398 prefixEnd_654398 := by exact prefixLift 654398
  have htrace : WordTrace (prefixWord ++ tailWord_654398) baseStart_654398 baseEnd_654398 := by
    simpa [prefixWord, tailWord_654398, baseEnd_654398] using wordTrace_append hprefix tailTrace_654398
  have hstable : (prefixWord ++ tailWord_654398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654398).length < 2 ^ (prefixWord ++ tailWord_654398).sum := by decide
  have hdescent : baseEnd_654398 < baseStart_654398 := by decide
  rcases family_descends (prefixWord ++ tailWord_654398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654401 : List Nat := [1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_654401 : Nat := 118140960795 + 654401 * 2 ^ 59
def prefixEnd_654401 : Nat := 4983230072969 + 3 ^ 40 * 654401 * 2
def baseEnd_654401 : Nat := 99562149269036855341621

theorem tailTrace_654401 : CollatzResearch.WordTrace tailWord_654401 prefixEnd_654401 99562149269036855341621 := by
  unfold tailWord_654401
  simp only [CollatzResearch.WordTrace]
  refine ⟨23867965302224414638019057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15911976868149609758679371 23867965302224414638019057)
  ·
    refine ⟨17900973976668310978514293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23867965302224414638019057 17900973976668310978514293)
    ·
      refine ⟨1678216310312654154235715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17900973976668310978514293 1678216310312654154235715)
      ·
        refine ⟨2517324465468981231353573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678216310312654154235715 2517324465468981231353573)
        ·
          refine ⟨471998337275433980878795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2517324465468981231353573 471998337275433980878795)
          ·
            refine ⟨707997505913150971318193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471998337275433980878795 707997505913150971318193)
            ·
              refine ⟨530998129434863228488645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707997505913150971318193 530998129434863228488645)
              ·
                refine ⟨99562149269036855341621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530998129434863228488645 99562149269036855341621)
                ·
                  rfl

theorem cell20_654401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_654401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654401 prefixEnd_654401 := by exact prefixLift 654401
  have htrace : WordTrace (prefixWord ++ tailWord_654401) baseStart_654401 baseEnd_654401 := by
    simpa [prefixWord, tailWord_654401, baseEnd_654401] using wordTrace_append hprefix tailTrace_654401
  have hstable : (prefixWord ++ tailWord_654401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654401).length < 2 ^ (prefixWord ++ tailWord_654401).sum := by decide
  have hdescent : baseEnd_654401 < baseStart_654401 := by decide
  rcases family_descends (prefixWord ++ tailWord_654401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654433 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_654433 : Nat := 118140960795 + 654433 * 2 ^ 59
def prefixEnd_654433 : Nat := 4983230072969 + 3 ^ 40 * 654433 * 2
def baseEnd_654433 : Nat := 298701053479060676958065

theorem tailTrace_654433 : CollatzResearch.WordTrace tailWord_654433 prefixEnd_654433 298701053479060676958065 := by
  unfold tailWord_654433
  simp only [CollatzResearch.WordTrace]
  refine ⟨23869132438108484103183953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15912754958738989402122635 23869132438108484103183953)
  ·
    refine ⟨17901849328581363077387965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23869132438108484103183953 17901849328581363077387965)
    ·
      refine ⟨6713193498218011154020487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17901849328581363077387965 6713193498218011154020487)
      ·
        refine ⟨10069790247327016731030731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713193498218011154020487 10069790247327016731030731)
        ·
          refine ⟨15104685370990525096546097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069790247327016731030731 15104685370990525096546097)
          ·
            refine ⟨11328514028242893822409573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15104685370990525096546097 11328514028242893822409573)
            ·
              refine ⟨2124096380295542591701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11328514028242893822409573 2124096380295542591701795)
              ·
                refine ⟨3186144570443313887552693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124096380295542591701795 3186144570443313887552693)
                ·
                  refine ⟨298701053479060676958065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3186144570443313887552693 298701053479060676958065)
                  ·
                    rfl

theorem cell20_654433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_654433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654433 prefixEnd_654433 := by exact prefixLift 654433
  have htrace : WordTrace (prefixWord ++ tailWord_654433) baseStart_654433 baseEnd_654433 := by
    simpa [prefixWord, tailWord_654433, baseEnd_654433] using wordTrace_append hprefix tailTrace_654433
  have hstable : (prefixWord ++ tailWord_654433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654433).length < 2 ^ (prefixWord ++ tailWord_654433).sum := by decide
  have hdescent : baseEnd_654433 < baseStart_654433 := by decide
  rcases family_descends (prefixWord ++ tailWord_654433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654446 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_654446 : Nat := 118140960795 + 654446 * 2 ^ 59
def prefixEnd_654446 : Nat := 4983230072969 + 3 ^ 40 * 654446 * 2
def baseEnd_654446 : Nat := 298706987033290409524679

theorem tailTrace_654446 : CollatzResearch.WordTrace tailWord_654446 prefixEnd_654446 298706987033290409524679 := by
  unfold tailWord_654446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983700823382673415425899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15913071058040924882271461 2983700823382673415425899)
  ·
    refine ⟨4475551235074010123138849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2983700823382673415425899 4475551235074010123138849)
    ·
      refine ⟨3356663426305507592354137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4475551235074010123138849 3356663426305507592354137)
      ·
        refine ⟨2517497569729130694265603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3356663426305507592354137 2517497569729130694265603)
        ·
          refine ⟨3776246354593696041398405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517497569729130694265603 3776246354593696041398405)
          ·
            refine ⟨708046191486318007762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3776246354593696041398405 708046191486318007762201)
            ·
              refine ⟨531034643614738505821651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708046191486318007762201 531034643614738505821651)
              ·
                refine ⟨796551965422107758732477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531034643614738505821651 796551965422107758732477)
                ·
                  refine ⟨298706987033290409524679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796551965422107758732477 298706987033290409524679)
                  ·
                    rfl

theorem cell20_654446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_654446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654446 prefixEnd_654446 := by exact prefixLift 654446
  have htrace : WordTrace (prefixWord ++ tailWord_654446) baseStart_654446 baseEnd_654446 := by
    simpa [prefixWord, tailWord_654446, baseEnd_654446] using wordTrace_append hprefix tailTrace_654446
  have hstable : (prefixWord ++ tailWord_654446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654446).length < 2 ^ (prefixWord ++ tailWord_654446).sum := by decide
  have hdescent : baseEnd_654446 < baseStart_654446 := by decide
  rcases family_descends (prefixWord ++ tailWord_654446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654450 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_654450 : Nat := 118140960795 + 654450 * 2 ^ 59
def prefixEnd_654450 : Nat := 4983230072969 + 3 ^ 40 * 654450 * 2
def baseEnd_654450 : Nat := 298708812742284173391329

theorem tailTrace_654450 : CollatzResearch.WordTrace tailWord_654450 prefixEnd_654450 298708812742284173391329 := by
  unfold tailWord_654450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967438119761724001638201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15913168319364597337701869 5967438119761724001638201)
  ·
    refine ⟨4475578589821293001228651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5967438119761724001638201 4475578589821293001228651)
    ·
      refine ⟨6713367884731939501842977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475578589821293001228651 6713367884731939501842977)
      ·
        refine ⟨5035025913548954626382233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6713367884731939501842977 5035025913548954626382233)
        ·
          refine ⟨3776269435161715969786675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5035025913548954626382233 3776269435161715969786675)
          ·
            refine ⟨5664404152742573954680013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776269435161715969786675 5664404152742573954680013)
            ·
              refine ⟨2124151557278465233005005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664404152742573954680013 2124151557278465233005005)
              ·
                refine ⟨796556833979424462376877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124151557278465233005005 796556833979424462376877)
                ·
                  refine ⟨298708812742284173391329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796556833979424462376877 298708812742284173391329)
                  ·
                    rfl

theorem cell20_654450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_654450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654450 prefixEnd_654450 := by exact prefixLift 654450
  have htrace : WordTrace (prefixWord ++ tailWord_654450) baseStart_654450 baseEnd_654450 := by
    simpa [prefixWord, tailWord_654450, baseEnd_654450] using wordTrace_append hprefix tailTrace_654450
  have hstable : (prefixWord ++ tailWord_654450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654450).length < 2 ^ (prefixWord ++ tailWord_654450).sum := by decide
  have hdescent : baseEnd_654450 < baseStart_654450 := by decide
  rcases family_descends (prefixWord ++ tailWord_654450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654474 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_654474 : Nat := 118140960795 + 654474 * 2 ^ 59
def prefixEnd_654474 : Nat := 4983230072969 + 3 ^ 40 * 654474 * 2
def baseEnd_654474 : Nat := 298719766996246756591231

theorem tailTrace_654474 : CollatzResearch.WordTrace tailWord_654474 prefixEnd_654474 298719766996246756591231 := by
  unfold tailWord_654474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967656957739987026356619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15913751887306632070284317 5967656957739987026356619)
  ·
    refine ⟨8951485436609980539534929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5967656957739987026356619 8951485436609980539534929)
    ·
      refine ⟨6713614077457485404651197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8951485436609980539534929 6713614077457485404651197)
      ·
        refine ⟨2517605279046557026744199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6713614077457485404651197 2517605279046557026744199)
        ·
          refine ⟨3776407918569835540116299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517605279046557026744199 3776407918569835540116299)
          ·
            refine ⟨5664611877854753310174449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776407918569835540116299 5664611877854753310174449)
            ·
              refine ⟨4248458908391064982630837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5664611877854753310174449 4248458908391064982630837)
              ·
                refine ⟨398293022661662342121641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4248458908391064982630837 398293022661662342121641)
                ·
                  refine ⟨298719766996246756591231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398293022661662342121641 298719766996246756591231)
                  ·
                    rfl

theorem cell20_654474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_654474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654474 prefixEnd_654474 := by exact prefixLift 654474
  have htrace : WordTrace (prefixWord ++ tailWord_654474) baseStart_654474 baseEnd_654474 := by
    simpa [prefixWord, tailWord_654474, baseEnd_654474] using wordTrace_append hprefix tailTrace_654474
  have hstable : (prefixWord ++ tailWord_654474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654474).length < 2 ^ (prefixWord ++ tailWord_654474).sum := by decide
  have hdescent : baseEnd_654474 < baseStart_654474 := by decide
  rcases family_descends (prefixWord ++ tailWord_654474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654488 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_654488 : Nat := 118140960795 + 654488 * 2 ^ 59
def prefixEnd_654488 : Nat := 4983230072969 + 3 ^ 40 * 654488 * 2
def baseEnd_654488 : Nat := 298726156977724930124507

theorem tailTrace_654488 : CollatzResearch.WordTrace tailWord_654488 prefixEnd_654488 298726156977724930124507 := by
  unfold tailWord_654488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935569226454614248218059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15914092301939485664290745 11935569226454614248218059)
  ·
    refine ⟨17903353839681921372327089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11935569226454614248218059 17903353839681921372327089)
    ·
      refine ⟨13427515379761441029245317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17903353839681921372327089 13427515379761441029245317)
      ·
        refine ⟨2517659133705270192983497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13427515379761441029245317 2517659133705270192983497)
        ·
          refine ⟨1888244350278952644737623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2517659133705270192983497 1888244350278952644737623)
          ·
            refine ⟨2832366525418428967106435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888244350278952644737623 2832366525418428967106435)
            ·
              refine ⟨4248549788127643450659653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832366525418428967106435 4248549788127643450659653)
              ·
                refine ⟨796603085273933146998685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4248549788127643450659653 796603085273933146998685)
                ·
                  refine ⟨298726156977724930124507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796603085273933146998685 298726156977724930124507)
                  ·
                    rfl

theorem cell20_654488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_654488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654488 prefixEnd_654488 := by exact prefixLift 654488
  have htrace : WordTrace (prefixWord ++ tailWord_654488) baseStart_654488 baseEnd_654488 := by
    simpa [prefixWord, tailWord_654488, baseEnd_654488] using wordTrace_append hprefix tailTrace_654488
  have hstable : (prefixWord ++ tailWord_654488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654488).length < 2 ^ (prefixWord ++ tailWord_654488).sum := by decide
  have hdescent : baseEnd_654488 < baseStart_654488 := by decide
  rcases family_descends (prefixWord ++ tailWord_654488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654498 : List Nat := [3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_654498 : Nat := 118140960795 + 654498 * 2 ^ 59
def prefixEnd_654498 : Nat := 4983230072969 + 3 ^ 40 * 654498 * 2
def baseEnd_654498 : Nat := 99576907083403113263711

theorem tailTrace_654498 : CollatzResearch.WordTrace tailWord_654498 prefixEnd_654498 99576907083403113263711 := by
  unfold tailWord_654498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967875795718250051075037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15914335455248666802866765 5967875795718250051075037)
  ·
    refine ⟨2237953423394343769153139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5967875795718250051075037 2237953423394343769153139)
    ·
      refine ⟨3356930135091515653729709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237953423394343769153139 3356930135091515653729709)
      ·
        refine ⟨1258848800659318370148641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3356930135091515653729709 1258848800659318370148641)
        ·
          refine ⟨944136600494488777611481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258848800659318370148641 944136600494488777611481)
          ·
            refine ⟨708102450370866583208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944136600494488777611481 708102450370866583208611)
            ·
              refine ⟨1062153675556299874812917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708102450370866583208611 1062153675556299874812917)
              ·
                refine ⟨99576907083403113263711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1062153675556299874812917 99576907083403113263711)
                ·
                  rfl

theorem cell20_654498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_654498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654498 prefixEnd_654498 := by exact prefixLift 654498
  have htrace : WordTrace (prefixWord ++ tailWord_654498) baseStart_654498 baseEnd_654498 := by
    simpa [prefixWord, tailWord_654498, baseEnd_654498] using wordTrace_append hprefix tailTrace_654498
  have hstable : (prefixWord ++ tailWord_654498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654498).length < 2 ^ (prefixWord ++ tailWord_654498).sum := by decide
  have hdescent : baseEnd_654498 < baseStart_654498 := by decide
  rcases family_descends (prefixWord ++ tailWord_654498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654529 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 2]
def baseStart_654529 : Nat := 118140960795 + 654529 * 2 ^ 59
def prefixEnd_654529 : Nat := 4983230072969 + 3 ^ 40 * 654529 * 2
def baseEnd_654529 : Nat := 298744870494911009757673

theorem tailTrace_654529 : CollatzResearch.WordTrace tailWord_654529 prefixEnd_654529 298744870494911009757673 := by
  unfold tailWord_654529
  simp only [CollatzResearch.WordTrace]
  refine ⟨23872633845760692498678641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15915089230507128332452427 23872633845760692498678641)
  ·
    refine ⟨17904475384320519374008981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23872633845760692498678641 17904475384320519374008981)
    ·
      refine ⟨839272283640024345656671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17904475384320519374008981 839272283640024345656671)
      ·
        refine ⟨1258908425460036518485007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839272283640024345656671 1258908425460036518485007)
        ·
          refine ⟨1888362638190054777727511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258908425460036518485007 1888362638190054777727511)
          ·
            refine ⟨2832543957285082166591267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888362638190054777727511 2832543957285082166591267)
            ·
              refine ⟨4248815935927623249886901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832543957285082166591267 4248815935927623249886901)
              ·
                refine ⟨398326493993214679676897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4248815935927623249886901 398326493993214679676897)
                ·
                  refine ⟨298744870494911009757673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398326493993214679676897 298744870494911009757673)
                  ·
                    rfl

theorem cell20_654529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_654529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654529 prefixEnd_654529 := by exact prefixLift 654529
  have htrace : WordTrace (prefixWord ++ tailWord_654529) baseStart_654529 baseEnd_654529 := by
    simpa [prefixWord, tailWord_654529, baseEnd_654529] using wordTrace_append hprefix tailTrace_654529
  have hstable : (prefixWord ++ tailWord_654529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654529).length < 2 ^ (prefixWord ++ tailWord_654529).sum := by decide
  have hdescent : baseEnd_654529 < baseStart_654529 := by decide
  rcases family_descends (prefixWord ++ tailWord_654529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654580 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_654580 : Nat := 118140960795 + 654580 * 2 ^ 59
def prefixEnd_654580 : Nat := 4983230072969 + 3 ^ 40 * 654580 * 2
def baseEnd_654580 : Nat := 298768148284581499057465

theorem tailTrace_654580 : CollatzResearch.WordTrace tailWord_654580 prefixEnd_654580 298768148284581499057465 := by
  unfold tailWord_654580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937246984287964104392597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15916329312383952139190129 11937246984287964104392597)
  ·
    refine ⟨559558452388498317393403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11937246984287964104392597 559558452388498317393403)
    ·
      refine ⟨839337678582747476090105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559558452388498317393403 839337678582747476090105)
      ·
        refine ⟨629503258937060607067579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839337678582747476090105 629503258937060607067579)
        ·
          refine ⟨944254888405590910601369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629503258937060607067579 944254888405590910601369)
          ·
            refine ⟨708191166304193182951027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944254888405590910601369 708191166304193182951027)
            ·
              refine ⟨1062286749456289774426541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708191166304193182951027 1062286749456289774426541)
              ·
                refine ⟨398357531046108665409953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062286749456289774426541 398357531046108665409953)
                ·
                  refine ⟨298768148284581499057465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398357531046108665409953 298768148284581499057465)
                  ·
                    rfl

theorem cell20_654580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_654580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654580 prefixEnd_654580 := by exact prefixLift 654580
  have htrace : WordTrace (prefixWord ++ tailWord_654580) baseStart_654580 baseEnd_654580 := by
    simpa [prefixWord, tailWord_654580, baseEnd_654580] using wordTrace_append hprefix tailTrace_654580
  have hstable : (prefixWord ++ tailWord_654580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654580).length < 2 ^ (prefixWord ++ tailWord_654580).sum := by decide
  have hdescent : baseEnd_654580 < baseStart_654580 := by decide
  rcases family_descends (prefixWord ++ tailWord_654580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654616 : List Nat := [2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_654616 : Nat := 118140960795 + 654616 * 2 ^ 59
def prefixEnd_654616 : Nat := 4983230072969 + 3 ^ 40 * 654616 * 2
def baseEnd_654616 : Nat := 99594859888508457952439

theorem tailTrace_654616 : CollatzResearch.WordTrace tailWord_654616 prefixEnd_654616 99594859888508457952439 := by
  unfold tailWord_654616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937903498222753178547851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15917204664297004238063801 11937903498222753178547851)
  ·
    refine ⟨17906855247334129767821777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937903498222753178547851 17906855247334129767821777)
    ·
      refine ⟨13430141435500597325866333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17906855247334129767821777 13430141435500597325866333)
      ·
        refine ⟨5036303038312723997199875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13430141435500597325866333 5036303038312723997199875)
        ·
          refine ⟨7554454557469085995799813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036303038312723997199875 7554454557469085995799813)
          ·
            refine ⟨1416460229525453624212465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7554454557469085995799813 1416460229525453624212465)
            ·
              refine ⟨1062345172144090218159349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416460229525453624212465 1062345172144090218159349)
              ·
                refine ⟨99594859888508457952439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1062345172144090218159349 99594859888508457952439)
                ·
                  rfl

theorem cell20_654616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_654616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654616 prefixEnd_654616 := by exact prefixLift 654616
  have htrace : WordTrace (prefixWord ++ tailWord_654616) baseStart_654616 baseEnd_654616 := by
    simpa [prefixWord, tailWord_654616, baseEnd_654616] using wordTrace_append hprefix tailTrace_654616
  have hstable : (prefixWord ++ tailWord_654616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654616).length < 2 ^ (prefixWord ++ tailWord_654616).sum := by decide
  have hdescent : baseEnd_654616 < baseStart_654616 := by decide
  rcases family_descends (prefixWord ++ tailWord_654616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654657 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_654657 : Nat := 118140960795 + 654657 * 2 ^ 59
def prefixEnd_654657 : Nat := 4983230072969 + 3 ^ 40 * 654657 * 2
def baseEnd_654657 : Nat := 298803293182711453490483

theorem tailTrace_654657 : CollatzResearch.WordTrace tailWord_654657 prefixEnd_654657 298803293182711453490483 := by
  unfold tailWord_654657
  simp only [CollatzResearch.WordTrace]
  refine ⟨23877302389296970359338225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15918201592864646906225483 23877302389296970359338225)
  ·
    refine ⟨17907976791972727769503669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23877302389296970359338225 17907976791972727769503669)
    ·
      refine ⟨1678872824247443228390969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17907976791972727769503669 1678872824247443228390969)
      ·
        refine ⟨1259154618185582421293227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678872824247443228390969 1259154618185582421293227)
        ·
          refine ⟨1888731927278373631939841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259154618185582421293227 1888731927278373631939841)
          ·
            refine ⟨1416548945458780223954881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888731927278373631939841 1416548945458780223954881)
            ·
              refine ⟨1062411709094085167966161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416548945458780223954881 1062411709094085167966161)
              ·
                refine ⟨796808781820563875974621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062411709094085167966161 796808781820563875974621)
                ·
                  refine ⟨298803293182711453490483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796808781820563875974621 298803293182711453490483)
                  ·
                    rfl

theorem cell20_654657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_654657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654657 prefixEnd_654657 := by exact prefixLift 654657
  have htrace : WordTrace (prefixWord ++ tailWord_654657) baseStart_654657 baseEnd_654657 := by
    simpa [prefixWord, tailWord_654657, baseEnd_654657] using wordTrace_append hprefix tailTrace_654657
  have hstable : (prefixWord ++ tailWord_654657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654657).length < 2 ^ (prefixWord ++ tailWord_654657).sum := by decide
  have hdescent : baseEnd_654657 < baseStart_654657 := by decide
  rcases family_descends (prefixWord ++ tailWord_654657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654660 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_654660 : Nat := 118140960795 + 654660 * 2 ^ 59
def prefixEnd_654660 : Nat := 4983230072969 + 3 ^ 40 * 654660 * 2
def baseEnd_654660 : Nat := 298804662464456776390471

theorem tailTrace_654660 : CollatzResearch.WordTrace tailWord_654660 prefixEnd_654660 298804662464456776390471 := by
  unfold tailWord_654660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11938705904143050935848717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15918274538857401247798289 11938705904143050935848717)
  ·
    refine ⟨4477014714053644100943269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11938705904143050935848717 4477014714053644100943269)
    ·
      refine ⟨839440258885058268926863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4477014714053644100943269 839440258885058268926863)
      ·
        refine ⟨1259160388327587403390295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839440258885058268926863 1259160388327587403390295)
        ·
          refine ⟨1888740582491381105085443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259160388327587403390295 1888740582491381105085443)
          ·
            refine ⟨2833110873737071657628165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888740582491381105085443 2833110873737071657628165)
            ·
              refine ⟨531208288825700935805281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2833110873737071657628165 531208288825700935805281)
              ·
                refine ⟨398406216619275701853961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531208288825700935805281 398406216619275701853961)
                ·
                  refine ⟨298804662464456776390471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398406216619275701853961 298804662464456776390471)
                  ·
                    rfl

theorem cell20_654660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_654660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654660 prefixEnd_654660 := by exact prefixLift 654660
  have htrace : WordTrace (prefixWord ++ tailWord_654660) baseStart_654660 baseEnd_654660 := by
    simpa [prefixWord, tailWord_654660, baseEnd_654660] using wordTrace_append hprefix tailTrace_654660
  have hstable : (prefixWord ++ tailWord_654660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654660).length < 2 ^ (prefixWord ++ tailWord_654660).sum := by decide
  have hdescent : baseEnd_654660 < baseStart_654660 := by decide
  rcases family_descends (prefixWord ++ tailWord_654660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654706 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_654706 : Nat := 118140960795 + 654706 * 2 ^ 59
def prefixEnd_654706 : Nat := 4983230072969 + 3 ^ 40 * 654706 * 2
def baseEnd_654706 : Nat := 298825658117885060856949

theorem tailTrace_654706 : CollatzResearch.WordTrace tailWord_654706 prefixEnd_654706 298825658117885060856949 := by
  unfold tailWord_654706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969772391529862931967993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15919393044079634485247981 5969772391529862931967993)
  ·
    refine ⟨4477329293647397198975995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5969772391529862931967993 4477329293647397198975995)
    ·
      refine ⟨6715993940471095798463993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477329293647397198975995 6715993940471095798463993)
      ·
        refine ⟨5036995455353321848847995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6715993940471095798463993 5036995455353321848847995)
        ·
          refine ⟨7555493183029982773271993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036995455353321848847995 7555493183029982773271993)
          ·
            refine ⟨5666619887272487079953995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7555493183029982773271993 5666619887272487079953995)
            ·
              refine ⟨8499929830908730619930993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5666619887272487079953995 8499929830908730619930993)
              ·
                refine ⟨6374947373181547964948245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8499929830908730619930993 6374947373181547964948245)
                ·
                  refine ⟨298825658117885060856949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6374947373181547964948245 298825658117885060856949)
                  ·
                    rfl

theorem cell20_654706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_654706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654706 prefixEnd_654706 := by exact prefixLift 654706
  have htrace : WordTrace (prefixWord ++ tailWord_654706) baseStart_654706 baseEnd_654706 := by
    simpa [prefixWord, tailWord_654706, baseEnd_654706] using wordTrace_append hprefix tailTrace_654706
  have hstable : (prefixWord ++ tailWord_654706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654706).length < 2 ^ (prefixWord ++ tailWord_654706).sum := by decide
  have hdescent : baseEnd_654706 < baseStart_654706 := by decide
  rcases family_descends (prefixWord ++ tailWord_654706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654723 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_654723 : Nat := 118140960795 + 654723 * 2 ^ 59
def prefixEnd_654723 : Nat := 4983230072969 + 3 ^ 40 * 654723 * 2
def baseEnd_654723 : Nat := 298833417381108557290213

theorem tailTrace_654723 : CollatzResearch.WordTrace tailWord_654723 prefixEnd_654723 298833417381108557290213 := by
  unfold tailWord_654723
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879709607057863631240823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15919806404705242420827215 23879709607057863631240823)
  ·
    refine ⟨35819564410586795446861235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23879709607057863631240823 35819564410586795446861235)
    ·
      refine ⟨53729346615880193170291853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35819564410586795446861235 53729346615880193170291853)
      ·
        refine ⟨20148504980955072438859445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53729346615880193170291853 20148504980955072438859445)
        ·
          refine ⟨1888922341964538041143073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20148504980955072438859445 1888922341964538041143073)
          ·
            refine ⟨1416691756473403530857305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888922341964538041143073 1416691756473403530857305)
            ·
              refine ⟨1062518817355052648142979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416691756473403530857305 1062518817355052648142979)
              ·
                refine ⟨1593778226032578972214469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062518817355052648142979 1593778226032578972214469)
                ·
                  refine ⟨298833417381108557290213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593778226032578972214469 298833417381108557290213)
                  ·
                    rfl

theorem cell20_654723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_654723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654723 prefixEnd_654723 := by exact prefixLift 654723
  have htrace : WordTrace (prefixWord ++ tailWord_654723) baseStart_654723 baseEnd_654723 := by
    simpa [prefixWord, tailWord_654723, baseEnd_654723] using wordTrace_append hprefix tailTrace_654723
  have hstable : (prefixWord ++ tailWord_654723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654723).length < 2 ^ (prefixWord ++ tailWord_654723).sum := by decide
  have hdescent : baseEnd_654723 < baseStart_654723 := by decide
  rcases family_descends (prefixWord ++ tailWord_654723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654775 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_654775 : Nat := 118140960795 + 654775 * 2 ^ 59
def prefixEnd_654775 : Nat := 4983230072969 + 3 ^ 40 * 654775 * 2
def baseEnd_654775 : Nat := 298857151598027487556667

theorem tailTrace_654775 : CollatzResearch.WordTrace tailWord_654775 prefixEnd_654775 298857151598027487556667 := by
  unfold tailWord_654775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23881606202869476512133779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15921070801912984341422519 23881606202869476512133779)
  ·
    refine ⟨35822409304304214768200669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23881606202869476512133779 35822409304304214768200669)
    ·
      refine ⟨13433403489114080538075251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35822409304304214768200669 13433403489114080538075251)
      ·
        refine ⟨20150105233671120807112877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433403489114080538075251 20150105233671120807112877)
        ·
          refine ⟨7556289462626670302667329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20150105233671120807112877 7556289462626670302667329)
          ·
            refine ⟨5667217096970002727000497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7556289462626670302667329 5667217096970002727000497)
            ·
              refine ⟨4250412822727502045250373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667217096970002727000497 4250412822727502045250373)
              ·
                refine ⟨796952404261406633484445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4250412822727502045250373 796952404261406633484445)
                ·
                  refine ⟨298857151598027487556667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796952404261406633484445 298857151598027487556667)
                  ·
                    rfl

theorem cell20_654775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_654775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654775 prefixEnd_654775 := by exact prefixLift 654775
  have htrace : WordTrace (prefixWord ++ tailWord_654775) baseStart_654775 baseEnd_654775 := by
    simpa [prefixWord, tailWord_654775, baseEnd_654775] using wordTrace_append hprefix tailTrace_654775
  have hstable : (prefixWord ++ tailWord_654775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654775).length < 2 ^ (prefixWord ++ tailWord_654775).sum := by decide
  have hdescent : baseEnd_654775 < baseStart_654775 := by decide
  rcases family_descends (prefixWord ++ tailWord_654775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654788 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_654788 : Nat := 118140960795 + 654788 * 2 ^ 59
def prefixEnd_654788 : Nat := 4983230072969 + 3 ^ 40 * 654788 * 2
def baseEnd_654788 : Nat := 298863085152257220123281

theorem tailTrace_654788 : CollatzResearch.WordTrace tailWord_654788 prefixEnd_654788 298863085152257220123281 := by
  unfold tailWord_654788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941040175911189866178509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15921386901214919821571345 11941040175911189866178509)
  ·
    refine ⟨4477890065966696199816941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11941040175911189866178509 4477890065966696199816941)
    ·
      refine ⟨1679208774737511074931353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4477890065966696199816941 1679208774737511074931353)
      ·
        refine ⟨1259406581053133306198515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1679208774737511074931353 1259406581053133306198515)
        ·
          refine ⟨1889109871579699959297773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259406581053133306198515 1889109871579699959297773)
          ·
            refine ⟨708416201842387484736665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1889109871579699959297773 708416201842387484736665)
            ·
              refine ⟨531312151381790613552499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708416201842387484736665 531312151381790613552499)
              ·
                refine ⟨796968227072685920328749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531312151381790613552499 796968227072685920328749)
                ·
                  refine ⟨298863085152257220123281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796968227072685920328749 298863085152257220123281)
                  ·
                    rfl

theorem cell20_654788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_654788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654788 prefixEnd_654788 := by exact prefixLift 654788
  have htrace : WordTrace (prefixWord ++ tailWord_654788) baseStart_654788 baseEnd_654788 := by
    simpa [prefixWord, tailWord_654788, baseEnd_654788] using wordTrace_append hprefix tailTrace_654788
  have hstable : (prefixWord ++ tailWord_654788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654788).length < 2 ^ (prefixWord ++ tailWord_654788).sum := by decide
  have hdescent : baseEnd_654788 < baseStart_654788 := by decide
  rcases family_descends (prefixWord ++ tailWord_654788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654829 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 2]
def baseStart_654829 : Nat := 118140960795 + 654829 * 2 ^ 59
def prefixEnd_654829 : Nat := 4983230072969 + 3 ^ 40 * 654829 * 2
def baseEnd_654829 : Nat := 298881798669443299756447

theorem tailTrace_654829 : CollatzResearch.WordTrace tailWord_654829 prefixEnd_654829 298881798669443299756447 := by
  unfold tailWord_654829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23883575744673843734599541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15922383829782562489733027 23883575744673843734599541)
  ·
    refine ⟨2239085226063172850118707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23883575744673843734599541 2239085226063172850118707)
    ·
      refine ⟨3358627839094759275178061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239085226063172850118707 3358627839094759275178061)
      ·
        refine ⟨1259485439660534728191773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3358627839094759275178061 1259485439660534728191773)
        ·
          refine ⟨472307039872700523071915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1259485439660534728191773 472307039872700523071915)
          ·
            refine ⟨708460559809050784607873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472307039872700523071915 708460559809050784607873)
            ·
              refine ⟨531345419856788088455905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708460559809050784607873 531345419856788088455905)
              ·
                refine ⟨398509064892591066341929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531345419856788088455905 398509064892591066341929)
                ·
                  refine ⟨298881798669443299756447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398509064892591066341929 298881798669443299756447)
                  ·
                    rfl

theorem cell20_654829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_654829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654829 prefixEnd_654829 := by exact prefixLift 654829
  have htrace : WordTrace (prefixWord ++ tailWord_654829) baseStart_654829 baseEnd_654829 := by
    simpa [prefixWord, tailWord_654829, baseEnd_654829] using wordTrace_append hprefix tailTrace_654829
  have hstable : (prefixWord ++ tailWord_654829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654829).length < 2 ^ (prefixWord ++ tailWord_654829).sum := by decide
  have hdescent : baseEnd_654829 < baseStart_654829 := by decide
  rcases family_descends (prefixWord ++ tailWord_654829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654830 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_654830 : Nat := 118140960795 + 654830 * 2 ^ 59
def prefixEnd_654830 : Nat := 4983230072969 + 3 ^ 40 * 654830 * 2
def baseEnd_654830 : Nat := 298882255096691740723109

theorem tailTrace_654830 : CollatzResearch.WordTrace tailWord_654830 prefixEnd_654830 298882255096691740723109 := by
  unfold tailWord_654830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985451527208777613173243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15922408145113480603590629 2985451527208777613173243)
  ·
    refine ⟨4478177290813166419759865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2985451527208777613173243 4478177290813166419759865)
    ·
      refine ⟨3358632968109874814819899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4478177290813166419759865 3358632968109874814819899)
      ·
        refine ⟨5037949452164812222229849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358632968109874814819899 5037949452164812222229849)
        ·
          refine ⟨3778462089123609166672387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5037949452164812222229849 3778462089123609166672387)
          ·
            refine ⟨5667693133685413750008581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778462089123609166672387 5667693133685413750008581)
            ·
              refine ⟨1062692462566015078126609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5667693133685413750008581 1062692462566015078126609)
              ·
                refine ⟨797019346924511308594957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062692462566015078126609 797019346924511308594957)
                ·
                  refine ⟨298882255096691740723109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797019346924511308594957 298882255096691740723109)
                  ·
                    rfl

theorem cell20_654830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_654830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654830 prefixEnd_654830 := by exact prefixLift 654830
  have htrace : WordTrace (prefixWord ++ tailWord_654830) baseStart_654830 baseEnd_654830 := by
    simpa [prefixWord, tailWord_654830, baseEnd_654830] using wordTrace_append hprefix tailTrace_654830
  have hstable : (prefixWord ++ tailWord_654830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654830).length < 2 ^ (prefixWord ++ tailWord_654830).sum := by decide
  have hdescent : baseEnd_654830 < baseStart_654830 := by decide
  rcases family_descends (prefixWord ++ tailWord_654830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654833 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 2]
def baseStart_654833 : Nat := 118140960795 + 654833 * 2 ^ 59
def prefixEnd_654833 : Nat := 4983230072969 + 3 ^ 40 * 654833 * 2
def baseEnd_654833 : Nat := 298883624378437063623097

theorem tailTrace_654833 : CollatzResearch.WordTrace tailWord_654833 prefixEnd_654833 298883624378437063623097 := by
  unfold tailWord_654833
  simp only [CollatzResearch.WordTrace]
  refine ⟨23883721636659352417745153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15922481091106234945163435 23883721636659352417745153)
  ·
    refine ⟨17912791227494514313308865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23883721636659352417745153 17912791227494514313308865)
    ·
      refine ⟨13434593420620885734981649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17912791227494514313308865 13434593420620885734981649)
      ·
        refine ⟨10075945065465664301236237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13434593420620885734981649 10075945065465664301236237)
        ·
          refine ⟨3778479399549624112963589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10075945065465664301236237 3778479399549624112963589)
          ·
            refine ⟨708464887415554521180673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3778479399549624112963589 708464887415554521180673)
            ·
              refine ⟨531348665561665890885505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708464887415554521180673 531348665561665890885505)
              ·
                refine ⟨398511499171249418164129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531348665561665890885505 398511499171249418164129)
                ·
                  refine ⟨298883624378437063623097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398511499171249418164129 298883624378437063623097)
                  ·
                    rfl

theorem cell20_654833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_654833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654833 prefixEnd_654833 := by exact prefixLift 654833
  have htrace : WordTrace (prefixWord ++ tailWord_654833) baseStart_654833 baseEnd_654833 := by
    simpa [prefixWord, tailWord_654833, baseEnd_654833] using wordTrace_append hprefix tailTrace_654833
  have hstable : (prefixWord ++ tailWord_654833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654833).length < 2 ^ (prefixWord ++ tailWord_654833).sum := by decide
  have hdescent : baseEnd_654833 < baseStart_654833 := by decide
  rcases family_descends (prefixWord ++ tailWord_654833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654858 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_654858 : Nat := 118140960795 + 654858 * 2 ^ 59
def prefixEnd_654858 : Nat := 4983230072969 + 3 ^ 40 * 654858 * 2
def baseEnd_654858 : Nat := 298895035059648087789661

theorem tailTrace_654858 : CollatzResearch.WordTrace tailWord_654858 prefixEnd_654858 298895035059648087789661 := by
  unfold tailWord_654858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971158365392195421851307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15923088974379187791603485 5971158365392195421851307)
  ·
    refine ⟨8956737548088293132776961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971158365392195421851307 8956737548088293132776961)
    ·
      refine ⟨6717553161066219849582721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8956737548088293132776961 6717553161066219849582721)
      ·
        refine ⟨5038164870799664887187041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6717553161066219849582721 5038164870799664887187041)
        ·
          refine ⟨3778623653099748665390281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5038164870799664887187041 3778623653099748665390281)
          ·
            refine ⟨2833967739824811499042711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778623653099748665390281 2833967739824811499042711)
            ·
              refine ⟨4250951609737217248564067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833967739824811499042711 4250951609737217248564067)
              ·
                refine ⟨6376427414605825872846101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250951609737217248564067 6376427414605825872846101)
                ·
                  refine ⟨298895035059648087789661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6376427414605825872846101 298895035059648087789661)
                  ·
                    rfl

theorem cell20_654858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_654858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654858 prefixEnd_654858 := by exact prefixLift 654858
  have htrace : WordTrace (prefixWord ++ tailWord_654858) baseStart_654858 baseEnd_654858 := by
    simpa [prefixWord, tailWord_654858, baseEnd_654858] using wordTrace_append hprefix tailTrace_654858
  have hstable : (prefixWord ++ tailWord_654858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654858).length < 2 ^ (prefixWord ++ tailWord_654858).sum := by decide
  have hdescent : baseEnd_654858 < baseStart_654858 := by decide
  rcases family_descends (prefixWord ++ tailWord_654858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654902 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_654902 : Nat := 118140960795 + 654902 * 2 ^ 59
def prefixEnd_654902 : Nat := 4983230072969 + 3 ^ 40 * 654902 * 2
def baseEnd_654902 : Nat := 298915117858579490322815

theorem tailTrace_654902 : CollatzResearch.WordTrace tailWord_654902 prefixEnd_654902 298915117858579490322815 := by
  unfold tailWord_654902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492889892088086075125435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15924158848939584801337973 1492889892088086075125435)
  ·
    refine ⟨2239334838132129112688153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492889892088086075125435 2239334838132129112688153)
    ·
      refine ⟨1679501128599096834516115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2239334838132129112688153 1679501128599096834516115)
      ·
        refine ⟨2519251692898645251774173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679501128599096834516115 2519251692898645251774173)
        ·
          refine ⟨944719384836991969415315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2519251692898645251774173 944719384836991969415315)
          ·
            refine ⟨1417079077255487954122973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944719384836991969415315 1417079077255487954122973)
            ·
              refine ⟨531404653970807982796115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417079077255487954122973 531404653970807982796115)
              ·
                refine ⟨797106980956211974194173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531404653970807982796115 797106980956211974194173)
                ·
                  refine ⟨298915117858579490322815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797106980956211974194173 298915117858579490322815)
                  ·
                    rfl

theorem cell20_654902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_654902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654902 prefixEnd_654902 := by exact prefixLift 654902
  have htrace : WordTrace (prefixWord ++ tailWord_654902) baseStart_654902 baseEnd_654902 := by
    simpa [prefixWord, tailWord_654902, baseEnd_654902] using wordTrace_append hprefix tailTrace_654902
  have hstable : (prefixWord ++ tailWord_654902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654902).length < 2 ^ (prefixWord ++ tailWord_654902).sum := by decide
  have hdescent : baseEnd_654902 < baseStart_654902 := by decide
  rcases family_descends (prefixWord ++ tailWord_654902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654906 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_654906 : Nat := 118140960795 + 654906 * 2 ^ 59
def prefixEnd_654906 : Nat := 4983230072969 + 3 ^ 40 * 654906 * 2
def baseEnd_654906 : Nat := 298916943567573254189465

theorem tailTrace_654906 : CollatzResearch.WordTrace tailWord_654906 prefixEnd_654906 298916943567573254189465 := by
  unfold tailWord_654906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971596041348721471288143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15924256110263257256768381 5971596041348721471288143)
  ·
    refine ⟨8957394062023082206932215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971596041348721471288143 8957394062023082206932215)
    ·
      refine ⟨13436091093034623310398323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8957394062023082206932215 13436091093034623310398323)
      ·
        refine ⟨20154136639551934965597485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436091093034623310398323 20154136639551934965597485)
        ·
          refine ⟨7557801239831975612099057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20154136639551934965597485 7557801239831975612099057)
          ·
            refine ⟨5668350929873981709074293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7557801239831975612099057 5668350929873981709074293)
            ·
              refine ⟨531407899675685785225715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5668350929873981709074293 531407899675685785225715)
              ·
                refine ⟨797111849513528677838573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531407899675685785225715 797111849513528677838573)
                ·
                  refine ⟨298916943567573254189465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797111849513528677838573 298916943567573254189465)
                  ·
                    rfl

theorem cell20_654906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_654906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654906 prefixEnd_654906 := by exact prefixLift 654906
  have htrace : WordTrace (prefixWord ++ tailWord_654906) baseStart_654906 baseEnd_654906 := by
    simpa [prefixWord, tailWord_654906, baseEnd_654906] using wordTrace_append hprefix tailTrace_654906
  have hstable : (prefixWord ++ tailWord_654906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654906).length < 2 ^ (prefixWord ++ tailWord_654906).sum := by decide
  have hdescent : baseEnd_654906 < baseStart_654906 := by decide
  rcases family_descends (prefixWord ++ tailWord_654906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654930 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_654930 : Nat := 118140960795 + 654930 * 2 ^ 59
def prefixEnd_654930 : Nat := 4983230072969 + 3 ^ 40 * 654930 * 2
def baseEnd_654930 : Nat := 298927897821535837389367

theorem tailTrace_654930 : CollatzResearch.WordTrace tailWord_654930 prefixEnd_654930 298927897821535837389367 := by
  unfold tailWord_654930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971814879326984496006561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15924839678205291989350829 5971814879326984496006561)
  ·
    refine ⟨4478861159495238372004921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5971814879326984496006561 4478861159495238372004921)
    ·
      refine ⟨3359145869621428779003691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4478861159495238372004921 3359145869621428779003691)
      ·
        refine ⟨5038718804432143168505537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359145869621428779003691 5038718804432143168505537)
        ·
          refine ⟨3779039103324107376379153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5038718804432143168505537 3779039103324107376379153)
          ·
            refine ⟨2834279327493080532284365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779039103324107376379153 2834279327493080532284365)
            ·
              refine ⟨1062854747809905199606637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834279327493080532284365 1062854747809905199606637)
              ·
                refine ⟨398570530428714449852489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062854747809905199606637 398570530428714449852489)
                ·
                  refine ⟨298927897821535837389367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398570530428714449852489 298927897821535837389367)
                  ·
                    rfl

theorem cell20_654930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_654930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654930 prefixEnd_654930 := by exact prefixLift 654930
  have htrace : WordTrace (prefixWord ++ tailWord_654930) baseStart_654930 baseEnd_654930 := by
    simpa [prefixWord, tailWord_654930, baseEnd_654930] using wordTrace_append hprefix tailTrace_654930
  have hstable : (prefixWord ++ tailWord_654930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654930).length < 2 ^ (prefixWord ++ tailWord_654930).sum := by decide
  have hdescent : baseEnd_654930 < baseStart_654930 := by decide
  rcases family_descends (prefixWord ++ tailWord_654930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654951 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 2]
def baseStart_654951 : Nat := 118140960795 + 654951 * 2 ^ 59
def prefixEnd_654951 : Nat := 4983230072969 + 3 ^ 40 * 654951 * 2
def baseEnd_654951 : Nat := 298937482793753097689281

theorem tailTrace_654951 : CollatzResearch.WordTrace tailWord_654951 prefixEnd_654951 298937482793753097689281 := by
  unfold tailWord_654951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23888025450231858570540707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15925350300154572380360471 23888025450231858570540707)
  ·
    refine ⟨35832038175347787855811061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23888025450231858570540707 35832038175347787855811061)
    ·
      refine ⟨3359253578938855111482287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35832038175347787855811061 3359253578938855111482287)
      ·
        refine ⟨5038880368408282667223431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359253578938855111482287 5038880368408282667223431)
        ·
          refine ⟨7558320552612424000835147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038880368408282667223431 7558320552612424000835147)
          ·
            refine ⟨11337480828918636001252721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7558320552612424000835147 11337480828918636001252721)
            ·
              refine ⟨8503110621688977000939541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11337480828918636001252721 8503110621688977000939541)
              ·
                refine ⟨398583310391670796919041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8503110621688977000939541 398583310391670796919041)
                ·
                  refine ⟨298937482793753097689281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398583310391670796919041 298937482793753097689281)
                  ·
                    rfl

theorem cell20_654951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2].length) (baseStart_654951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654951 prefixEnd_654951 := by exact prefixLift 654951
  have htrace : WordTrace (prefixWord ++ tailWord_654951) baseStart_654951 baseEnd_654951 := by
    simpa [prefixWord, tailWord_654951, baseEnd_654951] using wordTrace_append hprefix tailTrace_654951
  have hstable : (prefixWord ++ tailWord_654951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654951).length < 2 ^ (prefixWord ++ tailWord_654951).sum := by decide
  have hdescent : baseEnd_654951 < baseStart_654951 := by decide
  rcases family_descends (prefixWord ++ tailWord_654951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654993 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_654993 : Nat := 118140960795 + 654993 * 2 ^ 59
def prefixEnd_654993 : Nat := 4983230072969 + 3 ^ 40 * 654993 * 2
def baseEnd_654993 : Nat := 298956652738187618289109

theorem tailTrace_654993 : CollatzResearch.WordTrace tailWord_654993 prefixEnd_654993 298956652738187618289109 := by
  unfold tailWord_654993
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889557316079699743569633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15926371544053133162379755 23889557316079699743569633)
  ·
    refine ⟨17917167987059774807677225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23889557316079699743569633 17917167987059774807677225)
    ·
      refine ⟨13437875990294831105757919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17917167987059774807677225 13437875990294831105757919)
      ·
        refine ⟨20156813985442246658636879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13437875990294831105757919 20156813985442246658636879)
        ·
          refine ⟨30235220978163369987955319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156813985442246658636879 30235220978163369987955319)
          ·
            refine ⟨45352831467245054981932979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30235220978163369987955319 45352831467245054981932979)
            ·
              refine ⟨68029247200867582472899469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45352831467245054981932979 68029247200867582472899469)
              ·
                refine ⟨25510967700325343427337301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68029247200867582472899469 25510967700325343427337301)
                ·
                  refine ⟨298956652738187618289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25510967700325343427337301 298956652738187618289109)
                  ·
                    rfl

theorem cell20_654993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_654993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654993 prefixEnd_654993 := by exact prefixLift 654993
  have htrace : WordTrace (prefixWord ++ tailWord_654993) baseStart_654993 baseEnd_654993 := by
    simpa [prefixWord, tailWord_654993, baseEnd_654993] using wordTrace_append hprefix tailTrace_654993
  have hstable : (prefixWord ++ tailWord_654993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654993).length < 2 ^ (prefixWord ++ tailWord_654993).sum := by decide
  have hdescent : baseEnd_654993 < baseStart_654993 := by decide
  rcases family_descends (prefixWord ++ tailWord_654993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654996 : List Nat := [2, 4, 2, 2, 2, 8]
def baseStart_654996 : Nat := 118140960795 + 654996 * 2 ^ 59
def prefixEnd_654996 : Nat := 4983230072969 + 3 ^ 40 * 654996 * 2
def baseEnd_654996 : Nat := 11072519334071590414411

theorem tailTrace_654996 : CollatzResearch.WordTrace tailWord_654996 prefixEnd_654996 11072519334071590414411 := by
  unfold tailWord_654996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944833367534415627964421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15926444490045887503952561 11944833367534415627964421)
  ·
    refine ⟨2239656256412702930243329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11944833367534415627964421 2239656256412702930243329)
    ·
      refine ⟨1679742192309527197682497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2239656256412702930243329 1679742192309527197682497)
      ·
        refine ⟨1259806644232145398261873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1679742192309527197682497 1259806644232145398261873)
        ·
          refine ⟨944854983174109048696405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259806644232145398261873 944854983174109048696405)
          ·
            refine ⟨11072519334071590414411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 944854983174109048696405 11072519334071590414411)
            ·
              rfl

theorem cell20_654996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 8].length) (baseStart_654996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_654996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_654996 prefixEnd_654996 := by exact prefixLift 654996
  have htrace : WordTrace (prefixWord ++ tailWord_654996) baseStart_654996 baseEnd_654996 := by
    simpa [prefixWord, tailWord_654996, baseEnd_654996] using wordTrace_append hprefix tailTrace_654996
  have hstable : (prefixWord ++ tailWord_654996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654996).length < 2 ^ (prefixWord ++ tailWord_654996).sum := by decide
  have hdescent : baseEnd_654996 < baseStart_654996 := by decide
  rcases family_descends (prefixWord ++ tailWord_654996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655030 : List Nat := [5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_655030 : Nat := 118140960795 + 655030 * 2 ^ 59
def prefixEnd_655030 : Nat := 4983230072969 + 3 ^ 40 * 655030 * 2
def baseEnd_655030 : Nat := 99657846848793311351875

theorem tailTrace_655030 : CollatzResearch.WordTrace tailWord_655030 prefixEnd_655030 99657846848793311351875 := by
  unfold tailWord_655030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493181676059103441416659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15927271211297103375111029 1493181676059103441416659)
  ·
    refine ⟨2239772514088655162124989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493181676059103441416659 2239772514088655162124989)
    ·
      refine ⟨839914692783245685796871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239772514088655162124989 839914692783245685796871)
      ·
        refine ⟨1259872039174868528695307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839914692783245685796871 1259872039174868528695307)
        ·
          refine ⟨1889808058762302793042961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259872039174868528695307 1889808058762302793042961)
          ·
            refine ⟨1417356044071727094782221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1889808058762302793042961 1417356044071727094782221)
            ·
              refine ⟨531508516526897660543333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417356044071727094782221 531508516526897660543333)
              ·
                refine ⟨99657846848793311351875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 531508516526897660543333 99657846848793311351875)
                ·
                  rfl

theorem cell20_655030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_655030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655030 prefixEnd_655030 := by exact prefixLift 655030
  have htrace : WordTrace (prefixWord ++ tailWord_655030) baseStart_655030 baseEnd_655030 := by
    simpa [prefixWord, tailWord_655030, baseEnd_655030] using wordTrace_append hprefix tailTrace_655030
  have hstable : (prefixWord ++ tailWord_655030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655030).length < 2 ^ (prefixWord ++ tailWord_655030).sum := by decide
  have hdescent : baseEnd_655030 < baseStart_655030 := by decide
  rcases family_descends (prefixWord ++ tailWord_655030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655034 : List Nat := [3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_655034 : Nat := 118140960795 + 655034 * 2 ^ 59
def prefixEnd_655034 : Nat := 4983230072969 + 3 ^ 40 * 655034 * 2
def baseEnd_655034 : Nat := 99658455418457899307425

theorem tailTrace_655034 : CollatzResearch.WordTrace tailWord_655034 prefixEnd_655034 99658455418457899307425 := by
  unfold tailWord_655034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5972763177232790936453039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15927368472620775830541437 5972763177232790936453039)
  ·
    refine ⟨8959144765849186404679559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5972763177232790936453039 8959144765849186404679559)
    ·
      refine ⟨13438717148773779607019339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959144765849186404679559 13438717148773779607019339)
      ·
        refine ⟨20158075723160669410529009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438717148773779607019339 20158075723160669410529009)
        ·
          refine ⟨15118556792370502057896757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20158075723160669410529009 15118556792370502057896757)
          ·
            refine ⟨1417364699284734567927821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15118556792370502057896757 1417364699284734567927821)
            ·
              refine ⟨531511762231775462972933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417364699284734567927821 531511762231775462972933)
              ·
                refine ⟨99658455418457899307425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 531511762231775462972933 99658455418457899307425)
                ·
                  rfl

theorem cell20_655034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_655034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655034 prefixEnd_655034 := by exact prefixLift 655034
  have htrace : WordTrace (prefixWord ++ tailWord_655034) baseStart_655034 baseEnd_655034 := by
    simpa [prefixWord, tailWord_655034, baseEnd_655034] using wordTrace_append hprefix tailTrace_655034
  have hstable : (prefixWord ++ tailWord_655034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655034).length < 2 ^ (prefixWord ++ tailWord_655034).sum := by decide
  have hdescent : baseEnd_655034 < baseStart_655034 := by decide
  rcases family_descends (prefixWord ++ tailWord_655034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655044 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_655044 : Nat := 118140960795 + 655044 * 2 ^ 59
def prefixEnd_655044 : Nat := 4983230072969 + 3 ^ 40 * 655044 * 2
def baseEnd_655044 : Nat := 298979930527858107588901

theorem tailTrace_655044 : CollatzResearch.WordTrace tailWord_655044 prefixEnd_655044 298979930527858107588901 := by
  unfold tailWord_655044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11945708719447467726838093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15927611625929956969117457 11945708719447467726838093)
  ·
    refine ⟨4479640769792800397564285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11945708719447467726838093 4479640769792800397564285)
    ·
      refine ⟨1679865288672300149086607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4479640769792800397564285 1679865288672300149086607)
      ·
        refine ⟨2519797933008450223629911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679865288672300149086607 2519797933008450223629911)
        ·
          refine ⟨3779696899512675335444867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519797933008450223629911 3779696899512675335444867)
          ·
            refine ⟨5669545349269013003167301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779696899512675335444867 5669545349269013003167301)
            ·
              refine ⟨1063039752987939938093869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5669545349269013003167301 1063039752987939938093869)
              ·
                refine ⟨398639907370477476785201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063039752987939938093869 398639907370477476785201)
                ·
                  refine ⟨298979930527858107588901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398639907370477476785201 298979930527858107588901)
                  ·
                    rfl

theorem cell20_655044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_655044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655044 prefixEnd_655044 := by exact prefixLift 655044
  have htrace : WordTrace (prefixWord ++ tailWord_655044) baseStart_655044 baseEnd_655044 := by
    simpa [prefixWord, tailWord_655044, baseEnd_655044] using wordTrace_append hprefix tailTrace_655044
  have hstable : (prefixWord ++ tailWord_655044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655044).length < 2 ^ (prefixWord ++ tailWord_655044).sum := by decide
  have hdescent : baseEnd_655044 < baseStart_655044 := by decide
  rcases family_descends (prefixWord ++ tailWord_655044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655058 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_655058 : Nat := 118140960795 + 655058 * 2 ^ 59
def prefixEnd_655058 : Nat := 4983230072969 + 3 ^ 40 * 655058 * 2
def baseEnd_655058 : Nat := 298986320509336281122177

theorem tailTrace_655058 : CollatzResearch.WordTrace tailWord_655058 prefixEnd_655058 298986320509336281122177 := by
  unfold tailWord_655058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5972982015211053961171457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15927952040562810563123885 5972982015211053961171457)
  ·
    refine ⟨4479736511408290470878593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5972982015211053961171457 4479736511408290470878593)
    ·
      refine ⟨3359802383556217853158945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479736511408290470878593 3359802383556217853158945)
      ·
        refine ⟨2519851787667163389869209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3359802383556217853158945 2519851787667163389869209)
        ·
          refine ⟨1889888840750372542401907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2519851787667163389869209 1889888840750372542401907)
          ·
            refine ⟨2834833261125558813602861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889888840750372542401907 2834833261125558813602861)
            ·
              refine ⟨1063062472922084555101073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834833261125558813602861 1063062472922084555101073)
              ·
                refine ⟨797296854691563416325805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063062472922084555101073 797296854691563416325805)
                ·
                  refine ⟨298986320509336281122177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797296854691563416325805 298986320509336281122177)
                  ·
                    rfl

theorem cell20_655058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_655058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655058 prefixEnd_655058 := by exact prefixLift 655058
  have htrace : WordTrace (prefixWord ++ tailWord_655058) baseStart_655058 baseEnd_655058 := by
    simpa [prefixWord, tailWord_655058, baseEnd_655058] using wordTrace_append hprefix tailTrace_655058
  have hstable : (prefixWord ++ tailWord_655058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655058).length < 2 ^ (prefixWord ++ tailWord_655058).sum := by decide
  have hdescent : baseEnd_655058 < baseStart_655058 := by decide
  rcases family_descends (prefixWord ++ tailWord_655058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655065 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 2]
def baseStart_655065 : Nat := 118140960795 + 655065 * 2 ^ 59
def prefixEnd_655065 : Nat := 4983230072969 + 3 ^ 40 * 655065 * 2
def baseEnd_655065 : Nat := 298989515500075367888815

theorem tailTrace_655065 : CollatzResearch.WordTrace tailWord_655065 prefixEnd_655065 298989515500075367888815 := by
  unfold tailWord_655065
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892183371818856040190649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928122247879237360127099 23892183371818856040190649)
  ·
    refine ⟨17919137528864142030142987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23892183371818856040190649 17919137528864142030142987)
    ·
      refine ⟨26878706293296213045214481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17919137528864142030142987 26878706293296213045214481)
      ·
        refine ⟨20159029719972159783910861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26878706293296213045214481 20159029719972159783910861)
        ·
          refine ⟨7559636144989559918966573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20159029719972159783910861 7559636144989559918966573)
          ·
            refine ⟨2834863554371084969612465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559636144989559918966573 2834863554371084969612465)
            ·
              refine ⟨2126147665778313727209349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834863554371084969612465 2126147665778313727209349)
              ·
                refine ⟨398652687333433823851753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2126147665778313727209349 398652687333433823851753)
                ·
                  refine ⟨298989515500075367888815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398652687333433823851753 298989515500075367888815)
                  ·
                    rfl

theorem cell20_655065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_655065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655065 prefixEnd_655065 := by exact prefixLift 655065
  have htrace : WordTrace (prefixWord ++ tailWord_655065) baseStart_655065 baseEnd_655065 := by
    simpa [prefixWord, tailWord_655065, baseEnd_655065] using wordTrace_append hprefix tailTrace_655065
  have hstable : (prefixWord ++ tailWord_655065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655065).length < 2 ^ (prefixWord ++ tailWord_655065).sum := by decide
  have hdescent : baseEnd_655065 < baseStart_655065 := by decide
  rcases family_descends (prefixWord ++ tailWord_655065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655075 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_655075 : Nat := 118140960795 + 655075 * 2 ^ 59
def prefixEnd_655075 : Nat := 4983230072969 + 3 ^ 40 * 655075 * 2
def baseEnd_655075 : Nat := 298994079772559777555441

theorem tailTrace_655075 : CollatzResearch.WordTrace tailWord_655075 prefixEnd_655075 298994079772559777555441 := by
  unfold tailWord_655075
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892548101782627748054679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928365401188418498703119 23892548101782627748054679)
  ·
    refine ⟨35838822152673941622082019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23892548101782627748054679 35838822152673941622082019)
    ·
      refine ⟨53758233229010912433123029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35838822152673941622082019 53758233229010912433123029)
      ·
        refine ⟨1259958591304943260151321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53758233229010912433123029 1259958591304943260151321)
        ·
          refine ⟨944968943478707445113491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259958591304943260151321 944968943478707445113491)
          ·
            refine ⟨1417453415218061167670237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944968943478707445113491 1417453415218061167670237)
            ·
              refine ⟨531545030706772937876339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417453415218061167670237 531545030706772937876339)
              ·
                refine ⟨797317546060159406814509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531545030706772937876339 797317546060159406814509)
                ·
                  refine ⟨298994079772559777555441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797317546060159406814509 298994079772559777555441)
                  ·
                    rfl

theorem cell20_655075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_655075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655075 prefixEnd_655075 := by exact prefixLift 655075
  have htrace : WordTrace (prefixWord ++ tailWord_655075) baseStart_655075 baseEnd_655075 := by
    simpa [prefixWord, tailWord_655075, baseEnd_655075] using wordTrace_append hprefix tailTrace_655075
  have hstable : (prefixWord ++ tailWord_655075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655075).length < 2 ^ (prefixWord ++ tailWord_655075).sum := by decide
  have hdescent : baseEnd_655075 < baseStart_655075 := by decide
  rcases family_descends (prefixWord ++ tailWord_655075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655086 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_655086 : Nat := 118140960795 + 655086 * 2 ^ 59
def prefixEnd_655086 : Nat := 4983230072969 + 3 ^ 40 * 655086 * 2
def baseEnd_655086 : Nat := 298999100472292628188729

theorem tailTrace_655086 : CollatzResearch.WordTrace tailWord_655086 prefixEnd_655086 298999100472292628188729 := by
  unfold tailWord_655086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986618663092847078338139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15928632869828517751136741 2986618663092847078338139)
  ·
    refine ⟨4479927994639270617507209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986618663092847078338139 4479927994639270617507209)
    ·
      refine ⟨3359945995979452963130407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479927994639270617507209 3359945995979452963130407)
      ·
        refine ⟨5039918993969179444695611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359945995979452963130407 5039918993969179444695611)
        ·
          refine ⟨7559878490953769167043417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039918993969179444695611 7559878490953769167043417)
          ·
            refine ⟨5669908868215326875282563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7559878490953769167043417 5669908868215326875282563)
            ·
              refine ⟨8504863302322990312923845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669908868215326875282563 8504863302322990312923845)
              ·
                refine ⟨1594661869185560683673221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8504863302322990312923845 1594661869185560683673221)
                ·
                  refine ⟨298999100472292628188729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594661869185560683673221 298999100472292628188729)
                  ·
                    rfl

theorem cell20_655086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_655086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655086 prefixEnd_655086 := by exact prefixLift 655086
  have htrace : WordTrace (prefixWord ++ tailWord_655086) baseStart_655086 baseEnd_655086 := by
    simpa [prefixWord, tailWord_655086, baseEnd_655086] using wordTrace_append hprefix tailTrace_655086
  have hstable : (prefixWord ++ tailWord_655086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655086).length < 2 ^ (prefixWord ++ tailWord_655086).sum := by decide
  have hdescent : baseEnd_655086 < baseStart_655086 := by decide
  rcases family_descends (prefixWord ++ tailWord_655086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655100 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_655100 : Nat := 118140960795 + 655100 * 2 ^ 59
def prefixEnd_655100 : Nat := 4983230072969 + 3 ^ 40 * 655100 * 2
def baseEnd_655100 : Nat := 299005490453770801722005

theorem tailTrace_655100 : CollatzResearch.WordTrace tailWord_655100 prefixEnd_655100 299005490453770801722005 := by
  unfold tailWord_655100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946729963346028508857377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15928973284461371345143169 11946729963346028508857377)
  ·
    refine ⟨8960047472509521381643033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11946729963346028508857377 8960047472509521381643033)
    ·
      refine ⟨6720035604382141036232275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8960047472509521381643033 6720035604382141036232275)
      ·
        refine ⟨10080053406573211554348413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720035604382141036232275 10080053406573211554348413)
        ·
          refine ⟨3780020027464954332880655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10080053406573211554348413 3780020027464954332880655)
          ·
            refine ⟨5670030041197431499320983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780020027464954332880655 5670030041197431499320983)
            ·
              refine ⟨8505045061796147248981475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670030041197431499320983 8505045061796147248981475)
              ·
                refine ⟨12757567592694220873472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505045061796147248981475 12757567592694220873472213)
                ·
                  refine ⟨299005490453770801722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12757567592694220873472213 299005490453770801722005)
                  ·
                    rfl

theorem cell20_655100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_655100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655100 prefixEnd_655100 := by exact prefixLift 655100
  have htrace : WordTrace (prefixWord ++ tailWord_655100) baseStart_655100 baseEnd_655100 := by
    simpa [prefixWord, tailWord_655100, baseEnd_655100] using wordTrace_append hprefix tailTrace_655100
  have hstable : (prefixWord ++ tailWord_655100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655100).length < 2 ^ (prefixWord ++ tailWord_655100).sum := by decide
  have hdescent : baseEnd_655100 < baseStart_655100 := by decide
  rcases family_descends (prefixWord ++ tailWord_655100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655103 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 2]
def baseStart_655103 : Nat := 118140960795 + 655103 * 2 ^ 59
def prefixEnd_655103 : Nat := 4983230072969 + 3 ^ 40 * 655103 * 2
def baseEnd_655103 : Nat := 299006859735516124621993

theorem tailTrace_655103 : CollatzResearch.WordTrace tailWord_655103 prefixEnd_655103 299006859735516124621993 := by
  unfold tailWord_655103
  simp only [CollatzResearch.WordTrace]
  refine ⟨23893569345681188530073963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15929046230454125686715975 23893569345681188530073963)
  ·
    refine ⟨35840354018521782795110945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23893569345681188530073963 35840354018521782795110945)
    ·
      refine ⟨26880265513891337096333209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35840354018521782795110945 26880265513891337096333209)
      ·
        refine ⟨20160199135418502822249907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26880265513891337096333209 20160199135418502822249907)
        ·
          refine ⟨30240298703127754233374861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20160199135418502822249907 30240298703127754233374861)
          ·
            refine ⟨11340112013672907837515573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30240298703127754233374861 11340112013672907837515573)
            ·
              refine ⟨1063135501281835109767085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11340112013672907837515573 1063135501281835109767085)
              ·
                refine ⟨398675812980688166162657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063135501281835109767085 398675812980688166162657)
                ·
                  refine ⟨299006859735516124621993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398675812980688166162657 299006859735516124621993)
                  ·
                    rfl

theorem cell20_655103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2].length) (baseStart_655103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655103 prefixEnd_655103 := by exact prefixLift 655103
  have htrace : WordTrace (prefixWord ++ tailWord_655103) baseStart_655103 baseEnd_655103 := by
    simpa [prefixWord, tailWord_655103, baseEnd_655103] using wordTrace_append hprefix tailTrace_655103
  have hstable : (prefixWord ++ tailWord_655103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655103).length < 2 ^ (prefixWord ++ tailWord_655103).sum := by decide
  have hdescent : baseEnd_655103 < baseStart_655103 := by decide
  rcases family_descends (prefixWord ++ tailWord_655103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655107 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_655107 : Nat := 118140960795 + 655107 * 2 ^ 59
def prefixEnd_655107 : Nat := 4983230072969 + 3 ^ 40 * 655107 * 2
def baseEnd_655107 : Nat := 299008685444509888488643

theorem tailTrace_655107 : CollatzResearch.WordTrace tailWord_655107 prefixEnd_655107 299008685444509888488643 := by
  unfold tailWord_655107
  simp only [CollatzResearch.WordTrace]
  refine ⟨23893715237666697213219575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15929143491777798142146383 23893715237666697213219575)
  ·
    refine ⟨35840572856500045819829363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23893715237666697213219575 35840572856500045819829363)
    ·
      refine ⟨53760859284750068729744045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35840572856500045819829363 53760859284750068729744045)
      ·
        refine ⟨20160322231781275773654017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53760859284750068729744045 20160322231781275773654017)
        ·
          refine ⟨15120241673835956830240513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20160322231781275773654017 15120241673835956830240513)
          ·
            refine ⟨11340181255376967622680385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15120241673835956830240513 11340181255376967622680385)
            ·
              refine ⟨8505135941532725717010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11340181255376967622680385 8505135941532725717010289)
              ·
                refine ⟨6378851956149544287757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8505135941532725717010289 6378851956149544287757717)
                ·
                  refine ⟨299008685444509888488643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6378851956149544287757717 299008685444509888488643)
                  ·
                    rfl

theorem cell20_655107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_655107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655107 prefixEnd_655107 := by exact prefixLift 655107
  have htrace : WordTrace (prefixWord ++ tailWord_655107) baseStart_655107 baseEnd_655107 := by
    simpa [prefixWord, tailWord_655107, baseEnd_655107] using wordTrace_append hprefix tailTrace_655107
  have hstable : (prefixWord ++ tailWord_655107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655107).length < 2 ^ (prefixWord ++ tailWord_655107).sum := by decide
  have hdescent : baseEnd_655107 < baseStart_655107 := by decide
  rcases family_descends (prefixWord ++ tailWord_655107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655186 : List Nat := [3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_655186 : Nat := 118140960795 + 655186 * 2 ^ 59
def prefixEnd_655186 : Nat := 4983230072969 + 3 ^ 40 * 655186 * 2
def baseEnd_655186 : Nat := 99681581065712241618329

theorem tailTrace_655186 : CollatzResearch.WordTrace tailWord_655186 prefixEnd_655186 99681581065712241618329 := by
  unfold tailWord_655186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974149151095123426336353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15931064402920329136896941 5974149151095123426336353)
  ·
    refine ⟨4480611863321342569752265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5974149151095123426336353 4480611863321342569752265)
    ·
      refine ⟨3360458897491006927314199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4480611863321342569752265 3360458897491006927314199)
      ·
        refine ⟨5040688346236510390971299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360458897491006927314199 5040688346236510390971299)
        ·
          refine ⟨7561032519354765586456949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040688346236510390971299 7561032519354765586456949)
          ·
            refine ⟨708846798689509273730339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7561032519354765586456949 708846798689509273730339)
            ·
              refine ⟨1063270198034263910595509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708846798689509273730339 1063270198034263910595509)
              ·
                refine ⟨99681581065712241618329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063270198034263910595509 99681581065712241618329)
                ·
                  rfl

theorem cell20_655186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_655186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655186 prefixEnd_655186 := by exact prefixLift 655186
  have htrace : WordTrace (prefixWord ++ tailWord_655186) baseStart_655186 baseEnd_655186 := by
    simpa [prefixWord, tailWord_655186, baseEnd_655186] using wordTrace_append hprefix tailTrace_655186
  have hstable : (prefixWord ++ tailWord_655186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655186).length < 2 ^ (prefixWord ++ tailWord_655186).sum := by decide
  have hdescent : baseEnd_655186 < baseStart_655186 := by decide
  rcases family_descends (prefixWord ++ tailWord_655186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655200 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_655200 : Nat := 118140960795 + 655200 * 2 ^ 59
def prefixEnd_655200 : Nat := 4983230072969 + 3 ^ 40 * 655200 * 2
def baseEnd_655200 : Nat := 299051133178614898388263

theorem tailTrace_655200 : CollatzResearch.WordTrace tailWord_655200 prefixEnd_655200 299051133178614898388263 := by
  unfold tailWord_655200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948553613164887048177527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15931404817553182730903369 11948553613164887048177527)
  ·
    refine ⟨17922830419747330572266291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11948553613164887048177527 17922830419747330572266291)
    ·
      refine ⟨26884245629620995858399437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17922830419747330572266291 26884245629620995858399437)
      ·
        refine ⟨10081592111107873446899789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26884245629620995858399437 10081592111107873446899789)
        ·
          refine ⟨3780597041665452542587421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10081592111107873446899789 3780597041665452542587421)
          ·
            refine ⟨1417723890624544703470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3780597041665452542587421 1417723890624544703470283)
            ·
              refine ⟨2126585835936817055205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417723890624544703470283 2126585835936817055205425)
              ·
                refine ⟨1594939376952612791404069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126585835936817055205425 1594939376952612791404069)
                ·
                  refine ⟨299051133178614898388263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594939376952612791404069 299051133178614898388263)
                  ·
                    rfl

theorem cell20_655200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_655200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655200 prefixEnd_655200 := by exact prefixLift 655200
  have htrace : WordTrace (prefixWord ++ tailWord_655200) baseStart_655200 baseEnd_655200 := by
    simpa [prefixWord, tailWord_655200, baseEnd_655200] using wordTrace_append hprefix tailTrace_655200
  have hstable : (prefixWord ++ tailWord_655200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655200).length < 2 ^ (prefixWord ++ tailWord_655200).sum := by decide
  have hdescent : baseEnd_655200 < baseStart_655200 := by decide
  rcases family_descends (prefixWord ++ tailWord_655200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655217 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 2]
def baseStart_655217 : Nat := 118140960795 + 655217 * 2 ^ 59
def prefixEnd_655217 : Nat := 4983230072969 + 3 ^ 40 * 655217 * 2
def baseEnd_655217 : Nat := 299058892441838394821527

theorem tailTrace_655217 : CollatzResearch.WordTrace tailWord_655217 prefixEnd_655217 299058892441838394821527 := by
  unfold tailWord_655217
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897727267268185999723905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15931818178178790666482603 23897727267268185999723905)
  ·
    refine ⟨17923295450451139499792929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23897727267268185999723905 17923295450451139499792929)
    ·
      refine ⟨13442471587838354624844697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17923295450451139499792929 13442471587838354624844697)
      ·
        refine ⟨10081853690878765968633523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13442471587838354624844697 10081853690878765968633523)
        ·
          refine ⟨15122780536318148952950285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081853690878765968633523 15122780536318148952950285)
          ·
            refine ⟨5671042701119305857356357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15122780536318148952950285 5671042701119305857356357)
            ·
              refine ⟨1063320506459869848254317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5671042701119305857356357 1063320506459869848254317)
              ·
                refine ⟨398745189922451193095369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063320506459869848254317 398745189922451193095369)
                ·
                  refine ⟨299058892441838394821527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398745189922451193095369 299058892441838394821527)
                  ·
                    rfl

theorem cell20_655217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_655217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655217 prefixEnd_655217 := by exact prefixLift 655217
  have htrace : WordTrace (prefixWord ++ tailWord_655217) baseStart_655217 baseEnd_655217 := by
    simpa [prefixWord, tailWord_655217, baseEnd_655217] using wordTrace_append hprefix tailTrace_655217
  have hstable : (prefixWord ++ tailWord_655217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655217).length < 2 ^ (prefixWord ++ tailWord_655217).sum := by decide
  have hdescent : baseEnd_655217 < baseStart_655217 := by decide
  rcases family_descends (prefixWord ++ tailWord_655217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655254 : List Nat := [5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_655254 : Nat := 118140960795 + 655254 * 2 ^ 59
def prefixEnd_655254 : Nat := 4983230072969 + 3 ^ 40 * 655254 * 2
def baseEnd_655254 : Nat := 99691926750010236862681

theorem tailTrace_655254 : CollatzResearch.WordTrace tailWord_655254 prefixEnd_655254 99691926750010236862681 := by
  unfold tailWord_655254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493692298008383832426301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15932717845422760879213877 1493692298008383832426301)
  ·
    refine ⟨560134611753143937159863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1493692298008383832426301 560134611753143937159863)
    ·
      refine ⟨840201917629715905739795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560134611753143937159863 840201917629715905739795)
      ·
        refine ⟨1260302876444573858609693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840201917629715905739795 1260302876444573858609693)
        ·
          refine ⟨472613578666715196978635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1260302876444573858609693 472613578666715196978635)
          ·
            refine ⟨708920368000072795467953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472613578666715196978635 708920368000072795467953)
            ·
              refine ⟨531690276000054596600965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708920368000072795467953 531690276000054596600965)
              ·
                refine ⟨99691926750010236862681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 531690276000054596600965 99691926750010236862681)
                ·
                  rfl

theorem cell20_655254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_655254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655254 prefixEnd_655254 := by exact prefixLift 655254
  have htrace : WordTrace (prefixWord ++ tailWord_655254) baseStart_655254 baseEnd_655254 := by
    simpa [prefixWord, tailWord_655254, baseEnd_655254] using wordTrace_append hprefix tailTrace_655254
  have hstable : (prefixWord ++ tailWord_655254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655254).length < 2 ^ (prefixWord ++ tailWord_655254).sum := by decide
  have hdescent : baseEnd_655254 < baseStart_655254 := by decide
  rcases family_descends (prefixWord ++ tailWord_655254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655293 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_655293 : Nat := 118140960795 + 655293 * 2 ^ 59
def prefixEnd_655293 : Nat := 4983230072969 + 3 ^ 40 * 655293 * 2
def baseEnd_655293 : Nat := 299093580912719908287883

theorem tailTrace_655293 : CollatzResearch.WordTrace tailWord_655293 prefixEnd_655293 299093580912719908287883 := by
  unfold tailWord_655293
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900499214992850979490533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15933666143328567319660355 23900499214992850979490533)
  ·
    refine ⟨4481343602811159558654475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23900499214992850979490533 4481343602811159558654475)
    ·
      refine ⟨6722015404216739337981713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481343602811159558654475 6722015404216739337981713)
      ·
        refine ⟨5041511553162554503486285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6722015404216739337981713 5041511553162554503486285)
        ·
          refine ⟨1890566832435957938807357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5041511553162554503486285 1890566832435957938807357)
          ·
            refine ⟨708962562163484227052759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1890566832435957938807357 708962562163484227052759)
            ·
              refine ⟨1063443843245226340579139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708962562163484227052759 1063443843245226340579139)
              ·
                refine ⟨1595165764867839510868709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063443843245226340579139 1595165764867839510868709)
                ·
                  refine ⟨299093580912719908287883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595165764867839510868709 299093580912719908287883)
                  ·
                    rfl

theorem cell20_655293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_655293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655293 prefixEnd_655293 := by exact prefixLift 655293
  have htrace : WordTrace (prefixWord ++ tailWord_655293) baseStart_655293 baseEnd_655293 := by
    simpa [prefixWord, tailWord_655293, baseEnd_655293] using wordTrace_append hprefix tailTrace_655293
  have hstable : (prefixWord ++ tailWord_655293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655293).length < 2 ^ (prefixWord ++ tailWord_655293).sum := by decide
  have hdescent : baseEnd_655293 < baseStart_655293 := by decide
  rcases family_descends (prefixWord ++ tailWord_655293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655341 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_655341 : Nat := 118140960795 + 655341 * 2 ^ 59
def prefixEnd_655341 : Nat := 4983230072969 + 3 ^ 40 * 655341 * 2
def baseEnd_655341 : Nat := 299115489420645074687687

theorem tailTrace_655341 : CollatzResearch.WordTrace tailWord_655341 prefixEnd_655341 299115489420645074687687 := by
  unfold tailWord_655341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23902249918818955177237877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15934833279212636784825251 23902249918818955177237877)
  ·
    refine ⟨2240835929889277047866051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23902249918818955177237877 2240835929889277047866051)
    ·
      refine ⟨3361253894833915571799077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240835929889277047866051 3361253894833915571799077)
      ·
        refine ⟨630235105281359169712327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3361253894833915571799077 630235105281359169712327)
        ·
          refine ⟨945352657922038754568491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630235105281359169712327 945352657922038754568491)
          ·
            refine ⟨1418028986883058131852737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945352657922038754568491 1418028986883058131852737)
            ·
              refine ⟨1063521740162293598889553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418028986883058131852737 1063521740162293598889553)
              ·
                refine ⟨797641305121720199167165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063521740162293598889553 797641305121720199167165)
                ·
                  refine ⟨299115489420645074687687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797641305121720199167165 299115489420645074687687)
                  ·
                    rfl

theorem cell20_655341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_655341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655341 prefixEnd_655341 := by exact prefixLift 655341
  have htrace : WordTrace (prefixWord ++ tailWord_655341) baseStart_655341 baseEnd_655341 := by
    simpa [prefixWord, tailWord_655341, baseEnd_655341] using wordTrace_append hprefix tailTrace_655341
  have hstable : (prefixWord ++ tailWord_655341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655341).length < 2 ^ (prefixWord ++ tailWord_655341).sum := by decide
  have hdescent : baseEnd_655341 < baseStart_655341 := by decide
  rcases family_descends (prefixWord ++ tailWord_655341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655400 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_655400 : Nat := 118140960795 + 655400 * 2 ^ 59
def prefixEnd_655400 : Nat := 4983230072969 + 3 ^ 40 * 655400 * 2
def baseEnd_655400 : Nat := 299142418628303091720779

theorem tailTrace_655400 : CollatzResearch.WordTrace tailWord_655400 prefixEnd_655400 299142418628303091720779 := by
  unfold tailWord_655400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952200912802604126817827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15936267883736805502423769 11952200912802604126817827)
  ·
    refine ⟨17928301369203906190226741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952200912802604126817827 17928301369203906190226741)
    ·
      refine ⟨1680778253362866205333757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17928301369203906190226741 1680778253362866205333757)
      ·
        refine ⟨630291845011074827000159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1680778253362866205333757 630291845011074827000159)
        ·
          refine ⟨945437767516612240500239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630291845011074827000159 945437767516612240500239)
          ·
            refine ⟨1418156651274918360750359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945437767516612240500239 1418156651274918360750359)
            ·
              refine ⟨2127234976912377541125539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418156651274918360750359 2127234976912377541125539)
              ·
                refine ⟨3190852465368566311688309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127234976912377541125539 3190852465368566311688309)
                ·
                  refine ⟨299142418628303091720779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3190852465368566311688309 299142418628303091720779)
                  ·
                    rfl

theorem cell20_655400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_655400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655400 prefixEnd_655400 := by exact prefixLift 655400
  have htrace : WordTrace (prefixWord ++ tailWord_655400) baseStart_655400 baseEnd_655400 := by
    simpa [prefixWord, tailWord_655400, baseEnd_655400] using wordTrace_append hprefix tailTrace_655400
  have hstable : (prefixWord ++ tailWord_655400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655400).length < 2 ^ (prefixWord ++ tailWord_655400).sum := by decide
  have hdescent : baseEnd_655400 < baseStart_655400 := by decide
  rcases family_descends (prefixWord ++ tailWord_655400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655404 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_655404 : Nat := 118140960795 + 655404 * 2 ^ 59
def prefixEnd_655404 : Nat := 4983230072969 + 3 ^ 40 * 655404 * 2
def baseEnd_655404 : Nat := 299144244337296855587429

theorem tailTrace_655404 : CollatzResearch.WordTrace tailWord_655404 prefixEnd_655404 299144244337296855587429 := by
  unfold tailWord_655404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952273858795358468390633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15936365145060477957854177 11952273858795358468390633)
  ·
    refine ⟨8964205394096518851292975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11952273858795358468390633 8964205394096518851292975)
    ·
      refine ⟨13446308091144778276939463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964205394096518851292975 13446308091144778276939463)
      ·
        refine ⟨20169462136717167415409195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446308091144778276939463 20169462136717167415409195)
        ·
          refine ⟨30254193205075751123113793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20169462136717167415409195 30254193205075751123113793)
          ·
            refine ⟨22690644903806813342335345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30254193205075751123113793 22690644903806813342335345)
            ·
              refine ⟨17017983677855110006751509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22690644903806813342335345 17017983677855110006751509)
              ·
                refine ⟨797717984899458281566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17017983677855110006751509 797717984899458281566477)
                ·
                  refine ⟨299144244337296855587429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797717984899458281566477 299144244337296855587429)
                  ·
                    rfl

theorem cell20_655404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_655404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655404 prefixEnd_655404 := by exact prefixLift 655404
  have htrace : WordTrace (prefixWord ++ tailWord_655404) baseStart_655404 baseEnd_655404 := by
    simpa [prefixWord, tailWord_655404, baseEnd_655404] using wordTrace_append hprefix tailTrace_655404
  have hstable : (prefixWord ++ tailWord_655404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655404).length < 2 ^ (prefixWord ++ tailWord_655404).sum := by decide
  have hdescent : baseEnd_655404 < baseStart_655404 := by decide
  rcases family_descends (prefixWord ++ tailWord_655404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655411 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_655411 : Nat := 118140960795 + 655411 * 2 ^ 59
def prefixEnd_655411 : Nat := 4983230072969 + 3 ^ 40 * 655411 * 2
def baseEnd_655411 : Nat := 299147439328035942354067

theorem tailTrace_655411 : CollatzResearch.WordTrace tailWord_655411 prefixEnd_655411 299147439328035942354067 := by
  unfold tailWord_655411
  simp only [CollatzResearch.WordTrace]
  refine ⟨23904803028565357132286087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15936535352376904754857391 23904803028565357132286087)
  ·
    refine ⟨35857204542848035698429131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23904803028565357132286087 35857204542848035698429131)
    ·
      refine ⟨53785806814272053547643697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35857204542848035698429131 53785806814272053547643697)
      ·
        refine ⟨40339355110704040160732773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53785806814272053547643697 40339355110704040160732773)
        ·
          refine ⟨7563629083257007530137395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40339355110704040160732773 7563629083257007530137395)
          ·
            refine ⟨11345443624885511295206093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7563629083257007530137395 11345443624885511295206093)
            ·
              refine ⟨4254541359332066735702285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11345443624885511295206093 4254541359332066735702285)
              ·
                refine ⟨1595453009749525025888357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4254541359332066735702285 1595453009749525025888357)
                ·
                  refine ⟨299147439328035942354067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595453009749525025888357 299147439328035942354067)
                  ·
                    rfl

theorem cell20_655411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_655411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655411 prefixEnd_655411 := by exact prefixLift 655411
  have htrace : WordTrace (prefixWord ++ tailWord_655411) baseStart_655411 baseEnd_655411 := by
    simpa [prefixWord, tailWord_655411, baseEnd_655411] using wordTrace_append hprefix tailTrace_655411
  have hstable : (prefixWord ++ tailWord_655411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655411).length < 2 ^ (prefixWord ++ tailWord_655411).sum := by decide
  have hdescent : baseEnd_655411 < baseStart_655411 := by decide
  rcases family_descends (prefixWord ++ tailWord_655411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655418 : List Nat := [3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_655418 : Nat := 118140960795 + 655418 * 2 ^ 59
def prefixEnd_655418 : Nat := 4983230072969 + 3 ^ 40 * 655418 * 2
def baseEnd_655418 : Nat := 99716878106258343040235

theorem tailTrace_655418 : CollatzResearch.WordTrace tailWord_655418 prefixEnd_655418 99716878106258343040235 := by
  unfold tailWord_655418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976264584884999331947727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15936705559693331551860605 5976264584884999331947727)
  ·
    refine ⟨8964396877327498997921591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5976264584884999331947727 8964396877327498997921591)
    ·
      refine ⟨13446595315991248496882387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964396877327498997921591 13446595315991248496882387)
      ·
        refine ⟨20169892973986872745323581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446595315991248496882387 20169892973986872745323581)
        ·
          refine ⟨7563709865245077279496343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20169892973986872745323581 7563709865245077279496343)
          ·
            refine ⟨11345564797867615919244515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7563709865245077279496343 11345564797867615919244515)
            ·
              refine ⟨17018347196801423878866773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11345564797867615919244515 17018347196801423878866773)
              ·
                refine ⟨99716878106258343040235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17018347196801423878866773 99716878106258343040235)
                ·
                  rfl

theorem cell20_655418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_655418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655418 prefixEnd_655418 := by exact prefixLift 655418
  have htrace : WordTrace (prefixWord ++ tailWord_655418) baseStart_655418 baseEnd_655418 := by
    simpa [prefixWord, tailWord_655418, baseEnd_655418] using wordTrace_append hprefix tailTrace_655418
  have hstable : (prefixWord ++ tailWord_655418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655418).length < 2 ^ (prefixWord ++ tailWord_655418).sum := by decide
  have hdescent : baseEnd_655418 < baseStart_655418 := by decide
  rcases family_descends (prefixWord ++ tailWord_655418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655445 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 2]
def baseStart_655445 : Nat := 118140960795 + 655445 * 2 ^ 59
def prefixEnd_655445 : Nat := 4983230072969 + 3 ^ 40 * 655445 * 2
def baseEnd_655445 : Nat := 299162957854482935220595

theorem tailTrace_655445 : CollatzResearch.WordTrace tailWord_655445 prefixEnd_655445 299162957854482935220595 := by
  unfold tailWord_655445
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906043110442180939023789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15937362073628120626015859 23906043110442180939023789)
  ·
    refine ⟨8964766166415817852133921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23906043110442180939023789 8964766166415817852133921)
    ·
      refine ⟨6723574624811863389100441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8964766166415817852133921 6723574624811863389100441)
      ·
        refine ⟨5042680968608897541825331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6723574624811863389100441 5042680968608897541825331)
        ·
          refine ⟨7564021452913346312737997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042680968608897541825331 7564021452913346312737997)
          ·
            refine ⟨2836508044842504867276749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7564021452913346312737997 2836508044842504867276749)
            ·
              refine ⟨1063690516815939325228781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2836508044842504867276749 1063690516815939325228781)
              ·
                refine ⟨398883943805977246960793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063690516815939325228781 398883943805977246960793)
                ·
                  refine ⟨299162957854482935220595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398883943805977246960793 299162957854482935220595)
                  ·
                    rfl

theorem cell20_655445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_655445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655445 prefixEnd_655445 := by exact prefixLift 655445
  have htrace : WordTrace (prefixWord ++ tailWord_655445) baseStart_655445 baseEnd_655445 := by
    simpa [prefixWord, tailWord_655445, baseEnd_655445] using wordTrace_append hprefix tailTrace_655445
  have hstable : (prefixWord ++ tailWord_655445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655445).length < 2 ^ (prefixWord ++ tailWord_655445).sum := by decide
  have hdescent : baseEnd_655445 < baseStart_655445 := by decide
  rcases family_descends (prefixWord ++ tailWord_655445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655456 : List Nat := [2, 1, 1, 3, 2, 3, 8]
def baseStart_655456 : Nat := 118140960795 + 655456 * 2 ^ 59
def prefixEnd_655456 : Nat := 4983230072969 + 3 ^ 40 * 655456 * 2
def baseEnd_655456 : Nat := 33240886506023976205987

theorem tailTrace_655456 : CollatzResearch.WordTrace tailWord_655456 prefixEnd_655456 33240886506023976205987 := by
  unfold tailWord_655456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11953222156701164908837111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15937629542268219878449481 11953222156701164908837111)
  ·
    refine ⟨17929833235051747363255667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11953222156701164908837111 17929833235051747363255667)
    ·
      refine ⟨26894749852577621044883501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17929833235051747363255667 26894749852577621044883501)
      ·
        refine ⟨10085531194716607891831313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26894749852577621044883501 10085531194716607891831313)
        ·
          refine ⟨7564148396037455918873485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10085531194716607891831313 7564148396037455918873485)
          ·
            refine ⟨2836555648514045969577557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7564148396037455918873485 2836555648514045969577557)
            ·
              refine ⟨33240886506023976205987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2836555648514045969577557 33240886506023976205987)
              ·
                rfl

theorem cell20_655456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_655456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655456 prefixEnd_655456 := by exact prefixLift 655456
  have htrace : WordTrace (prefixWord ++ tailWord_655456) baseStart_655456 baseEnd_655456 := by
    simpa [prefixWord, tailWord_655456, baseEnd_655456] using wordTrace_append hprefix tailTrace_655456
  have hstable : (prefixWord ++ tailWord_655456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655456).length < 2 ^ (prefixWord ++ tailWord_655456).sum := by decide
  have hdescent : baseEnd_655456 < baseStart_655456 := by decide
  rcases family_descends (prefixWord ++ tailWord_655456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655504 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_655504 : Nat := 118140960795 + 655504 * 2 ^ 59
def prefixEnd_655504 : Nat := 4983230072969 + 3 ^ 40 * 655504 * 2
def baseEnd_655504 : Nat := 299189887062140952253687

theorem tailTrace_655504 : CollatzResearch.WordTrace tailWord_655504 prefixEnd_655504 299189887062140952253687 := by
  unfold tailWord_655504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954097508614217007710783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15938796678152289343614377 11954097508614217007710783)
  ·
    refine ⟨17931146262921325511566175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954097508614217007710783 17931146262921325511566175)
    ·
      refine ⟨26896719394381988267349263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17931146262921325511566175 26896719394381988267349263)
      ·
        refine ⟨40345079091572982401023895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26896719394381988267349263 40345079091572982401023895)
        ·
          refine ⟨60517618637359473601535843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40345079091572982401023895 60517618637359473601535843)
          ·
            refine ⟨90776427956039210402303765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60517618637359473601535843 90776427956039210402303765)
            ·
              refine ⟨4255145060439337987607989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90776427956039210402303765 4255145060439337987607989)
              ·
                refine ⟨398919849416187936338249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4255145060439337987607989 398919849416187936338249)
                ·
                  refine ⟨299189887062140952253687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398919849416187936338249 299189887062140952253687)
                  ·
                    rfl

theorem cell20_655504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_655504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655504 prefixEnd_655504 := by exact prefixLift 655504
  have htrace : WordTrace (prefixWord ++ tailWord_655504) baseStart_655504 baseEnd_655504 := by
    simpa [prefixWord, tailWord_655504, baseEnd_655504] using wordTrace_append hprefix tailTrace_655504
  have hstable : (prefixWord ++ tailWord_655504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655504).length < 2 ^ (prefixWord ++ tailWord_655504).sum := by decide
  have hdescent : baseEnd_655504 < baseStart_655504 := by decide
  rcases family_descends (prefixWord ++ tailWord_655504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655511 : List Nat := [1, 1, 3, 3, 5, 7]
def baseStart_655511 : Nat := 118140960795 + 655511 * 2 ^ 59
def prefixEnd_655511 : Nat := 4983230072969 + 3 ^ 40 * 655511 * 2
def baseEnd_655511 : Nat := 11081225261217779222975

theorem tailTrace_655511 : CollatzResearch.WordTrace tailWord_655511 prefixEnd_655511 11081225261217779222975 := by
  unfold tailWord_655511
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908450328203074210926387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15938966885468716140617591 23908450328203074210926387)
  ·
    refine ⟨35862675492304611316389581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23908450328203074210926387 35862675492304611316389581)
    ·
      refine ⟨13448503309614229243646093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35862675492304611316389581 13448503309614229243646093)
      ·
        refine ⟨5043188741105335966367285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13448503309614229243646093 5043188741105335966367285)
        ·
          refine ⟨472798944478625246846933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5043188741105335966367285 472798944478625246846933)
          ·
            refine ⟨11081225261217779222975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 472798944478625246846933 11081225261217779222975)
            ·
              rfl

theorem cell20_655511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 7].length) (baseStart_655511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655511 prefixEnd_655511 := by exact prefixLift 655511
  have htrace : WordTrace (prefixWord ++ tailWord_655511) baseStart_655511 baseEnd_655511 := by
    simpa [prefixWord, tailWord_655511, baseEnd_655511] using wordTrace_append hprefix tailTrace_655511
  have hstable : (prefixWord ++ tailWord_655511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655511).length < 2 ^ (prefixWord ++ tailWord_655511).sum := by decide
  have hdescent : baseEnd_655511 < baseStart_655511 := by decide
  rcases family_descends (prefixWord ++ tailWord_655511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655514 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_655514 : Nat := 118140960795 + 655514 * 2 ^ 59
def prefixEnd_655514 : Nat := 4983230072969 + 3 ^ 40 * 655514 * 2
def baseEnd_655514 : Nat := 299194451334625361920313

theorem tailTrace_655514 : CollatzResearch.WordTrace tailWord_655514 prefixEnd_655514 299194451334625361920313 := by
  unfold tailWord_655514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977139936798051430821399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15939039831461470482190397 5977139936798051430821399)
  ·
    refine ⟨8965709905197077146232099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5977139936798051430821399 8965709905197077146232099)
    ·
      refine ⟨13448564857795615719348149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8965709905197077146232099 13448564857795615719348149)
      ·
        refine ⟨1260802955418338973688889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13448564857795615719348149 1260802955418338973688889)
        ·
          refine ⟨945602216563754230266667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260802955418338973688889 945602216563754230266667)
          ·
            refine ⟨1418403324845631345400001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945602216563754230266667 1418403324845631345400001)
            ·
              refine ⟨1063802493634223509050001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418403324845631345400001 1063802493634223509050001)
              ·
                refine ⟨797851870225667631787501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063802493634223509050001 797851870225667631787501)
                ·
                  refine ⟨299194451334625361920313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797851870225667631787501 299194451334625361920313)
                  ·
                    rfl

theorem cell20_655514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_655514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655514 prefixEnd_655514 := by exact prefixLift 655514
  have htrace : WordTrace (prefixWord ++ tailWord_655514) baseStart_655514 baseEnd_655514 := by
    simpa [prefixWord, tailWord_655514, baseEnd_655514] using wordTrace_append hprefix tailTrace_655514
  have hstable : (prefixWord ++ tailWord_655514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655514).length < 2 ^ (prefixWord ++ tailWord_655514).sum := by decide
  have hdescent : baseEnd_655514 < baseStart_655514 := by decide
  rcases family_descends (prefixWord ++ tailWord_655514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655521 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 2]
def baseStart_655521 : Nat := 118140960795 + 655521 * 2 ^ 59
def prefixEnd_655521 : Nat := 4983230072969 + 3 ^ 40 * 655521 * 2
def baseEnd_655521 : Nat := 299197646325364448686951

theorem tailTrace_655521 : CollatzResearch.WordTrace tailWord_655521 prefixEnd_655521 299197646325364448686951 := by
  unfold tailWord_655521
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908815058166845918790417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15939210038777897279193611 23908815058166845918790417)
  ·
    refine ⟨17931611293625134439092813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23908815058166845918790417 17931611293625134439092813)
    ·
      refine ⟨6724354235109425414659805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17931611293625134439092813 6724354235109425414659805)
      ·
        refine ⟨2521632838166034530497427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6724354235109425414659805 2521632838166034530497427)
        ·
          refine ⟨3782449257249051795746141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521632838166034530497427 3782449257249051795746141)
          ·
            refine ⟨1418418471468394423404803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3782449257249051795746141 1418418471468394423404803)
            ·
              refine ⟨2127627707202591635107205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418418471468394423404803 2127627707202591635107205)
              ·
                refine ⟨398930195100485931582601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2127627707202591635107205 398930195100485931582601)
                ·
                  refine ⟨299197646325364448686951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398930195100485931582601 299197646325364448686951)
                  ·
                    rfl

theorem cell20_655521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_655521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655521 prefixEnd_655521 := by exact prefixLift 655521
  have htrace : WordTrace (prefixWord ++ tailWord_655521) baseStart_655521 baseEnd_655521 := by
    simpa [prefixWord, tailWord_655521, baseEnd_655521] using wordTrace_append hprefix tailTrace_655521
  have hstable : (prefixWord ++ tailWord_655521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655521).length < 2 ^ (prefixWord ++ tailWord_655521).sum := by decide
  have hdescent : baseEnd_655521 < baseStart_655521 := by decide
  rcases family_descends (prefixWord ++ tailWord_655521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655525 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_655525 : Nat := 118140960795 + 655525 * 2 ^ 59
def prefixEnd_655525 : Nat := 4983230072969 + 3 ^ 40 * 655525 * 2
def baseEnd_655525 : Nat := 299199472034358212553601

theorem tailTrace_655525 : CollatzResearch.WordTrace tailWord_655525 prefixEnd_655525 299199472034358212553601 := by
  unfold tailWord_655525
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908960950152354601936029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15939307300101569734624019 23908960950152354601936029)
  ·
    refine ⟨8965860356307132975726011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23908960950152354601936029 8965860356307132975726011)
    ·
      refine ⟨13448790534460699463589017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8965860356307132975726011 13448790534460699463589017)
      ·
        refine ⟨10086592900845524597691763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13448790534460699463589017 10086592900845524597691763)
        ·
          refine ⟨15129889351268286896537645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086592900845524597691763 15129889351268286896537645)
          ·
            refine ⟨5673708506725607586201617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15129889351268286896537645 5673708506725607586201617)
            ·
              refine ⟨4255281380044205689651213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673708506725607586201617 4255281380044205689651213)
              ·
                refine ⟨1595730517516577133619205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255281380044205689651213 1595730517516577133619205)
                ·
                  refine ⟨299199472034358212553601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595730517516577133619205 299199472034358212553601)
                  ·
                    rfl

theorem cell20_655525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_655525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655525 prefixEnd_655525 := by exact prefixLift 655525
  have htrace : WordTrace (prefixWord ++ tailWord_655525) baseStart_655525 baseEnd_655525 := by
    simpa [prefixWord, tailWord_655525, baseEnd_655525] using wordTrace_append hprefix tailTrace_655525
  have hstable : (prefixWord ++ tailWord_655525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655525).length < 2 ^ (prefixWord ++ tailWord_655525).sum := by decide
  have hdescent : baseEnd_655525 < baseStart_655525 := by decide
  rcases family_descends (prefixWord ++ tailWord_655525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655539 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_655539 : Nat := 118140960795 + 655539 * 2 ^ 59
def prefixEnd_655539 : Nat := 4983230072969 + 3 ^ 40 * 655539 * 2
def baseEnd_655539 : Nat := 299205862015836386086877

theorem tailTrace_655539 : CollatzResearch.WordTrace tailWord_655539 prefixEnd_655539 299205862015836386086877 := by
  unfold tailWord_655539
  simp only [CollatzResearch.WordTrace]
  refine ⟨23909471572101634992945671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15939647714734423328630447 23909471572101634992945671)
  ·
    refine ⟨35864207358152452489418507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23909471572101634992945671 35864207358152452489418507)
    ·
      refine ⟨53796311037228678734127761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35864207358152452489418507 53796311037228678734127761)
      ·
        refine ⟨40347233277921509050595821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53796311037228678734127761 40347233277921509050595821)
        ·
          refine ⟨15130212479220565893973433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40347233277921509050595821 15130212479220565893973433)
          ·
            refine ⟨11347659359415424420480075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130212479220565893973433 11347659359415424420480075)
            ·
              refine ⟨17021489039123136630720113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347659359415424420480075 17021489039123136630720113)
              ·
                refine ⟨12766116779342352473040085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17021489039123136630720113 12766116779342352473040085)
                ·
                  refine ⟨299205862015836386086877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12766116779342352473040085 299205862015836386086877)
                  ·
                    rfl

theorem cell20_655539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_655539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655539 prefixEnd_655539 := by exact prefixLift 655539
  have htrace : WordTrace (prefixWord ++ tailWord_655539) baseStart_655539 baseEnd_655539 := by
    simpa [prefixWord, tailWord_655539, baseEnd_655539] using wordTrace_append hprefix tailTrace_655539
  have hstable : (prefixWord ++ tailWord_655539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655539).length < 2 ^ (prefixWord ++ tailWord_655539).sum := by decide
  have hdescent : baseEnd_655539 < baseStart_655539 := by decide
  rcases family_descends (prefixWord ++ tailWord_655539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655573 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_655573 : Nat := 118140960795 + 655573 * 2 ^ 59
def prefixEnd_655573 : Nat := 4983230072969 + 3 ^ 40 * 655573 * 2
def baseEnd_655573 : Nat := 299221380542283378953405

theorem tailTrace_655573 : CollatzResearch.WordTrace tailWord_655573 prefixEnd_655573 299221380542283378953405 := by
  unfold tailWord_655573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23910711653978458799683373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15940474435985639199788915 23910711653978458799683373)
  ·
    refine ⟨8966516870241922049881265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23910711653978458799683373 8966516870241922049881265)
    ·
      refine ⟨6724887652681441537410949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8966516870241922049881265 6724887652681441537410949)
      ·
        refine ⟨1260916434877770288264553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6724887652681441537410949 1260916434877770288264553)
        ·
          refine ⟨945687326158327716198415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260916434877770288264553 945687326158327716198415)
          ·
            refine ⟨1418530989237491574297623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945687326158327716198415 1418530989237491574297623)
            ·
              refine ⟨2127796483856237361446435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418530989237491574297623 2127796483856237361446435)
              ·
                refine ⟨3191694725784356042169653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127796483856237361446435 3191694725784356042169653)
                ·
                  refine ⟨299221380542283378953405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191694725784356042169653 299221380542283378953405)
                  ·
                    rfl

theorem cell20_655573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_655573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655573 prefixEnd_655573 := by exact prefixLift 655573
  have htrace : WordTrace (prefixWord ++ tailWord_655573) baseStart_655573 baseEnd_655573 := by
    simpa [prefixWord, tailWord_655573, baseEnd_655573] using wordTrace_append hprefix tailTrace_655573
  have hstable : (prefixWord ++ tailWord_655573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655573).length < 2 ^ (prefixWord ++ tailWord_655573).sum := by decide
  have hdescent : baseEnd_655573 < baseStart_655573 := by decide
  rcases family_descends (prefixWord ++ tailWord_655573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
