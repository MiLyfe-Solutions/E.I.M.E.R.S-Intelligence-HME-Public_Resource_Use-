import V185TrunkScan22Chunk278

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2485872 : List Nat := [2, 1, 1, 1, 6, 1, 2, 8]
def baseStart_2485872 : Nat := 118140960795 + 2485872 * 2 ^ 59
def prefixEnd_2485872 : Nat := 4983230072969 + 3 ^ 40 * 2485872 * 2
def baseEnd_2485872 : Nat := 94551643078044685042051

theorem tailTrace_2485872 : CollatzResearch.WordTrace tailWord_2485872 prefixEnd_2485872 94551643078044685042051 := by
  unfold tailWord_2485872
  simp only [CollatzResearch.WordTrace]
  refine ⟨45333600225058885991153935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60444800300078514654871913 45333600225058885991153935)
  ·
    refine ⟨68000400337588328986730903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45333600225058885991153935 68000400337588328986730903)
    ·
      refine ⟨102000600506382493480096355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68000400337588328986730903 102000600506382493480096355)
      ·
        refine ⟨153000900759573740220144533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102000600506382493480096355 153000900759573740220144533)
        ·
          refine ⟨7171917223105019072819275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153000900759573740220144533 7171917223105019072819275)
          ·
            refine ⟨10757875834657528609228913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171917223105019072819275 10757875834657528609228913)
            ·
              refine ⟨8068406875993146456921685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757875834657528609228913 8068406875993146456921685)
              ·
                refine ⟨94551643078044685042051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8068406875993146456921685 94551643078044685042051)
                ·
                  rfl

theorem cell22_2485872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_2485872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485872 prefixEnd_2485872 := by exact prefixLift 2485872
  have htrace : WordTrace (prefixWord ++ tailWord_2485872) baseStart_2485872 baseEnd_2485872 := by
    simpa [prefixWord, tailWord_2485872, baseEnd_2485872] using wordTrace_append hprefix tailTrace_2485872
  have hstable : (prefixWord ++ tailWord_2485872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485872).length < 2 ^ (prefixWord ++ tailWord_2485872).sum := by decide
  have hdescent : baseEnd_2485872 < baseStart_2485872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485874 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2485874 : Nat := 118140960795 + 2485874 * 2 ^ 59
def prefixEnd_2485874 : Nat := 4983230072969 + 3 ^ 40 * 2485874 * 2
def baseEnd_2485874 : Nat := 850965472343274826828453

theorem tailTrace_2485874 : CollatzResearch.WordTrace tailWord_2485874 prefixEnd_2485874 850965472343274826828453 := by
  unfold tailWord_2485874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666818349027631580970169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60444848930740350882587117 22666818349027631580970169)
  ·
    refine ⟨17000113761770723685727627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22666818349027631580970169 17000113761770723685727627)
    ·
      refine ⟨25500170642656085528591441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17000113761770723685727627 25500170642656085528591441)
      ·
        refine ⟨19125127981992064146443581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25500170642656085528591441 19125127981992064146443581)
        ·
          refine ⟨7171922993247024054916343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19125127981992064146443581 7171922993247024054916343)
          ·
            refine ⟨10757884489870536082374515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171922993247024054916343 10757884489870536082374515)
            ·
              refine ⟨16136826734805804123561773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10757884489870536082374515 16136826734805804123561773)
              ·
                refine ⟨6051310025552176546335665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16136826734805804123561773 6051310025552176546335665)
                ·
                  refine ⟨4538482519164132409751749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6051310025552176546335665 4538482519164132409751749)
                  ·
                    refine ⟨850965472343274826828453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538482519164132409751749 850965472343274826828453)
                    ·
                      rfl

theorem cell22_2485874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2485874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485874 prefixEnd_2485874 := by exact prefixLift 2485874
  have htrace : WordTrace (prefixWord ++ tailWord_2485874) baseStart_2485874 baseEnd_2485874 := by
    simpa [prefixWord, tailWord_2485874, baseEnd_2485874] using wordTrace_append hprefix tailTrace_2485874
  have hstable : (prefixWord ++ tailWord_2485874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485874).length < 2 ^ (prefixWord ++ tailWord_2485874).sum := by decide
  have hdescent : baseEnd_2485874 < baseStart_2485874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485906 : List Nat := [3, 2, 3, 1, 3, 2, 1, 7]
def baseStart_2485906 : Nat := 118140960795 + 2485906 * 2 ^ 59
def prefixEnd_2485906 : Nat := 4983230072969 + 3 ^ 40 * 2485906 * 2
def baseEnd_2485906 : Nat := 94552936288581934447595

theorem tailTrace_2485906 : CollatzResearch.WordTrace tailWord_2485906 prefixEnd_2485906 94552936288581934447595 := by
  unfold tailWord_2485906
  simp only [CollatzResearch.WordTrace]
  refine ⟨22667110132998648947261393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60445627021329730526030381 22667110132998648947261393)
  ·
    refine ⟨17000332599748986710446045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22667110132998648947261393 17000332599748986710446045)
    ·
      refine ⟨6375124724905870016417267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17000332599748986710446045 6375124724905870016417267)
      ·
        refine ⟨9562687087358805024625901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6375124724905870016417267 9562687087358805024625901)
        ·
          refine ⟨3586007657759551884234713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9562687087358805024625901 3586007657759551884234713)
          ·
            refine ⟨2689505743319663913176035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586007657759551884234713 2689505743319663913176035)
            ·
              refine ⟨4034258614979495869764053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689505743319663913176035 4034258614979495869764053)
              ·
                refine ⟨94552936288581934447595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4034258614979495869764053 94552936288581934447595)
                ·
                  rfl

theorem cell22_2485906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_2485906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485906 prefixEnd_2485906 := by exact prefixLift 2485906
  have htrace : WordTrace (prefixWord ++ tailWord_2485906) baseStart_2485906 baseEnd_2485906 := by
    simpa [prefixWord, tailWord_2485906, baseEnd_2485906] using wordTrace_append hprefix tailTrace_2485906
  have hstable : (prefixWord ++ tailWord_2485906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485906).length < 2 ^ (prefixWord ++ tailWord_2485906).sum := by decide
  have hdescent : baseEnd_2485906 < baseStart_2485906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485917 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2485917 : Nat := 118140960795 + 2485917 * 2 ^ 59
def prefixEnd_2485917 : Nat := 4983230072969 + 3 ^ 40 * 2485917 * 2
def baseEnd_2485917 : Nat := 283660064040679016001107

theorem tailTrace_2485917 : CollatzResearch.WordTrace tailWord_2485917 prefixEnd_2485917 283660064040679016001107 := by
  unfold tailWord_2485917
  simp only [CollatzResearch.WordTrace]
  refine ⟨90668841734954744667696005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60445894489969829778464003 90668841734954744667696005)
  ·
    refine ⟨17000407825304014625193001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90668841734954744667696005 17000407825304014625193001)
    ·
      refine ⟨12750305868978010968894751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17000407825304014625193001 12750305868978010968894751)
      ·
        refine ⟨19125458803467016453342127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12750305868978010968894751 19125458803467016453342127)
        ·
          refine ⟨28688188205200524680013191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19125458803467016453342127 28688188205200524680013191)
          ·
            refine ⟨43032282307800787020019787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28688188205200524680013191 43032282307800787020019787)
            ·
              refine ⟨64548423461701180530029681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43032282307800787020019787 64548423461701180530029681)
              ·
                refine ⟨48411317596275885397522261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64548423461701180530029681 48411317596275885397522261)
                ·
                  refine ⟨283660064040679016001107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48411317596275885397522261 283660064040679016001107)
                  ·
                    rfl

theorem cell22_2485917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2485917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485917 prefixEnd_2485917 := by exact prefixLift 2485917
  have htrace : WordTrace (prefixWord ++ tailWord_2485917) baseStart_2485917 baseEnd_2485917 := by
    simpa [prefixWord, tailWord_2485917, baseEnd_2485917] using wordTrace_append hprefix tailTrace_2485917
  have hstable : (prefixWord ++ tailWord_2485917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485917).length < 2 ^ (prefixWord ++ tailWord_2485917).sum := by decide
  have hdescent : baseEnd_2485917 < baseStart_2485917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485921 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2485921 : Nat := 118140960795 + 2485921 * 2 ^ 59
def prefixEnd_2485921 : Nat := 4983230072969 + 3 ^ 40 * 2485921 * 2
def baseEnd_2485921 : Nat := 850981561403782370903309

theorem tailTrace_2485921 : CollatzResearch.WordTrace tailWord_2485921 prefixEnd_2485921 850981561403782370903309 := by
  unfold tailWord_2485921
  simp only [CollatzResearch.WordTrace]
  refine ⟨90668987626940253350841617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60445991751293502233894411 90668987626940253350841617)
  ·
    refine ⟨68001740720205190013131213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90668987626940253350841617 68001740720205190013131213)
    ·
      refine ⟨25500652770076946254924205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68001740720205190013131213 25500652770076946254924205)
      ·
        refine ⟨9562744788778854845596577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25500652770076946254924205 9562744788778854845596577)
        ·
          refine ⟨7172058591584141134197433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9562744788778854845596577 7172058591584141134197433)
          ·
            refine ⟨5379043943688105850648075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7172058591584141134197433 5379043943688105850648075)
            ·
              refine ⟨8068565915532158775972113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379043943688105850648075 8068565915532158775972113)
              ·
                refine ⟨6051424436649119081979085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8068565915532158775972113 6051424436649119081979085)
                ·
                  refine ⟨2269284163743419655742157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6051424436649119081979085 2269284163743419655742157)
                  ·
                    refine ⟨850981561403782370903309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269284163743419655742157 850981561403782370903309)
                    ·
                      rfl

theorem cell22_2485921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2485921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485921 prefixEnd_2485921 := by exact prefixLift 2485921
  have htrace : WordTrace (prefixWord ++ tailWord_2485921) baseStart_2485921 baseEnd_2485921 := by
    simpa [prefixWord, tailWord_2485921, baseEnd_2485921] using wordTrace_append hprefix tailTrace_2485921
  have hstable : (prefixWord ++ tailWord_2485921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485921).length < 2 ^ (prefixWord ++ tailWord_2485921).sum := by decide
  have hdescent : baseEnd_2485921 < baseStart_2485921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485994 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2485994 : Nat := 118140960795 + 2485994 * 2 ^ 59
def prefixEnd_2485994 : Nat := 4983230072969 + 3 ^ 40 * 2485994 * 2
def baseEnd_2485994 : Nat := 851006550795634513828085

theorem tailTrace_2485994 : CollatzResearch.WordTrace tailWord_2485994 prefixEnd_2485994 851006550795634513828085 := by
  unfold tailWord_2485994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22667912538918946704562259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60447766770450524545499357 22667912538918946704562259)
  ·
    refine ⟨34001868808378420056843389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22667912538918946704562259 34001868808378420056843389)
    ·
      refine ⟨12750700803141907521316271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34001868808378420056843389 12750700803141907521316271)
      ·
        refine ⟨19126051204712861281974407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12750700803141907521316271 19126051204712861281974407)
        ·
          refine ⟨28689076807069291922961611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19126051204712861281974407 28689076807069291922961611)
          ·
            refine ⟨43033615210603937884442417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28689076807069291922961611 43033615210603937884442417)
            ·
              refine ⟨32275211407952953413331813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43033615210603937884442417 32275211407952953413331813)
              ·
                refine ⟨6051602138991178764999715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32275211407952953413331813 6051602138991178764999715)
                ·
                  refine ⟨9077403208486768147499573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051602138991178764999715 9077403208486768147499573)
                  ·
                    refine ⟨851006550795634513828085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9077403208486768147499573 851006550795634513828085)
                    ·
                      rfl

theorem cell22_2485994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2485994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485994 prefixEnd_2485994 := by exact prefixLift 2485994
  have htrace : WordTrace (prefixWord ++ tailWord_2485994) baseStart_2485994 baseEnd_2485994 := by
    simpa [prefixWord, tailWord_2485994, baseEnd_2485994] using wordTrace_append hprefix tailTrace_2485994
  have hstable : (prefixWord ++ tailWord_2485994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485994).length < 2 ^ (prefixWord ++ tailWord_2485994).sum := by decide
  have hdescent : baseEnd_2485994 < baseStart_2485994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485996 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_2485996 : Nat := 118140960795 + 2485996 * 2 ^ 59
def prefixEnd_2485996 : Nat := 4983230072969 + 3 ^ 40 * 2485996 * 2
def baseEnd_2485996 : Nat := 283669078478835725092693

theorem tailTrace_2485996 : CollatzResearch.WordTrace tailWord_2485996 prefixEnd_2485996 283669078478835725092693 := by
  unfold tailWord_2485996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335861550834270579910921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60447815401112360773214561 45335861550834270579910921)
  ·
    refine ⟨34001896163125702934933191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45335861550834270579910921 34001896163125702934933191)
    ·
      refine ⟨51002844244688554402399787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34001896163125702934933191 51002844244688554402399787)
      ·
        refine ⟨76504266367032831603599681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51002844244688554402399787 76504266367032831603599681)
        ·
          refine ⟨57378199775274623702699761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76504266367032831603599681 57378199775274623702699761)
          ·
            refine ⟨43033649831455967777024821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57378199775274623702699761 43033649831455967777024821)
            ·
              refine ⟨4034404671698996979096077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43033649831455967777024821 4034404671698996979096077)
              ·
                refine ⟨1512901751887123867161029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4034404671698996979096077 1512901751887123867161029)
                ·
                  refine ⟨283669078478835725092693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512901751887123867161029 283669078478835725092693)
                  ·
                    rfl

theorem cell22_2485996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_2485996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485996 prefixEnd_2485996 := by exact prefixLift 2485996
  have htrace : WordTrace (prefixWord ++ tailWord_2485996) baseStart_2485996 baseEnd_2485996 := by
    simpa [prefixWord, tailWord_2485996, baseEnd_2485996] using wordTrace_append hprefix tailTrace_2485996
  have hstable : (prefixWord ++ tailWord_2485996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485996).length < 2 ^ (prefixWord ++ tailWord_2485996).sum := by decide
  have hdescent : baseEnd_2485996 < baseStart_2485996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486007 : List Nat := [1, 1, 3, 1, 1, 1, 14]
def baseStart_2486007 : Nat := 118140960795 + 2486007 * 2 ^ 59
def prefixEnd_2486007 : Nat := 4983230072969 + 3 ^ 40 * 2486007 * 2
def baseEnd_2486007 : Nat := 31518925961529881972335

theorem tailTrace_2486007 : CollatzResearch.WordTrace tailWord_2486007 prefixEnd_2486007 31518925961529881972335 := by
  unfold tailWord_2486007
  simp only [CollatzResearch.WordTrace]
  refine ⟨90672124304628690038472275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60448082869752460025648183 90672124304628690038472275)
  ·
    refine ⟨136008186456943035057708413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90672124304628690038472275 136008186456943035057708413)
    ·
      refine ⟨51003069921353638146640655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136008186456943035057708413 51003069921353638146640655)
      ·
        refine ⟨76504604882030457219960983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51003069921353638146640655 76504604882030457219960983)
        ·
          refine ⟨114756907323045685829941475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76504604882030457219960983 114756907323045685829941475)
          ·
            refine ⟨172135360984568528744912213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114756907323045685829941475 172135360984568528744912213)
            ·
              refine ⟨31518925961529881972335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 172135360984568528744912213 31518925961529881972335)
              ·
                rfl

theorem cell22_2486007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 14].length) (baseStart_2486007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486007 prefixEnd_2486007 := by exact prefixLift 2486007
  have htrace : WordTrace (prefixWord ++ tailWord_2486007) baseStart_2486007 baseEnd_2486007 := by
    simpa [prefixWord, tailWord_2486007, baseEnd_2486007] using wordTrace_append hprefix tailTrace_2486007
  have hstable : (prefixWord ++ tailWord_2486007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486007).length < 2 ^ (prefixWord ++ tailWord_2486007).sum := by decide
  have hdescent : baseEnd_2486007 < baseStart_2486007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486024 : List Nat := [2, 1, 3, 2, 2, 1, 4, 7]
def baseStart_2486024 : Nat := 118140960795 + 2486024 * 2 ^ 59
def prefixEnd_2486024 : Nat := 4983230072969 + 3 ^ 40 * 2486024 * 2
def baseEnd_2486024 : Nat := 94557424489858270619777

theorem tailTrace_2486024 : CollatzResearch.WordTrace tailWord_2486024 prefixEnd_2486024 94557424489858270619777 := by
  unfold tailWord_2486024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45336372172783550970920563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60448496230378067961227417 45336372172783550970920563)
  ·
    refine ⟨68004558259175326456380845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45336372172783550970920563 68004558259175326456380845)
    ·
      refine ⟨25501709347190747421142817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68004558259175326456380845 25501709347190747421142817)
      ·
        refine ⟨19126282010393060565857113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25501709347190747421142817 19126282010393060565857113)
        ·
          refine ⟨14344711507794795424392835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19126282010393060565857113 14344711507794795424392835)
          ·
            refine ⟨21517067261692193136589253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14344711507794795424392835 21517067261692193136589253)
            ·
              refine ⟨4034450111567286213110485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21517067261692193136589253 4034450111567286213110485)
              ·
                refine ⟨94557424489858270619777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4034450111567286213110485 94557424489858270619777)
                ·
                  rfl

theorem cell22_2486024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_2486024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486024 prefixEnd_2486024 := by exact prefixLift 2486024
  have htrace : WordTrace (prefixWord ++ tailWord_2486024) baseStart_2486024 baseEnd_2486024 := by
    simpa [prefixWord, tailWord_2486024, baseEnd_2486024] using wordTrace_append hprefix tailTrace_2486024
  have hstable : (prefixWord ++ tailWord_2486024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486024).length < 2 ^ (prefixWord ++ tailWord_2486024).sum := by decide
  have hdescent : baseEnd_2486024 < baseStart_2486024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486028 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_2486028 : Nat := 118140960795 + 2486028 * 2 ^ 59
def prefixEnd_2486028 : Nat := 4983230072969 + 3 ^ 40 * 2486028 * 2
def baseEnd_2486028 : Nat := 851018189690469758477981

theorem tailTrace_2486028 : CollatzResearch.WordTrace tailWord_2486028 prefixEnd_2486028 851018189690469758477981 := by
  unfold tailWord_2486028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45336445118776305312493369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60448593491701740416657825 45336445118776305312493369)
  ·
    refine ⟨34002333839082228984370027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45336445118776305312493369 34002333839082228984370027)
    ·
      refine ⟨51003500758623343476555041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34002333839082228984370027 51003500758623343476555041)
      ·
        refine ⟨38252625568967507607416281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51003500758623343476555041 38252625568967507607416281)
        ·
          refine ⟨28689469176725630705562211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38252625568967507607416281 28689469176725630705562211)
          ·
            refine ⟨43034203765088446058343317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28689469176725630705562211 43034203765088446058343317)
            ·
              refine ⟨2017228301488520908984843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43034203765088446058343317 2017228301488520908984843)
              ·
                refine ⟨3025842452232781363477265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017228301488520908984843 3025842452232781363477265)
                ·
                  refine ⟨2269381839174586022607949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025842452232781363477265 2269381839174586022607949)
                  ·
                    refine ⟨851018189690469758477981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269381839174586022607949 851018189690469758477981)
                    ·
                      rfl

theorem cell22_2486028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_2486028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486028 prefixEnd_2486028 := by exact prefixLift 2486028
  have htrace : WordTrace (prefixWord ++ tailWord_2486028) baseStart_2486028 baseEnd_2486028 := by
    simpa [prefixWord, tailWord_2486028, baseEnd_2486028] using wordTrace_append hprefix tailTrace_2486028
  have hstable : (prefixWord ++ tailWord_2486028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486028).length < 2 ^ (prefixWord ++ tailWord_2486028).sum := by decide
  have hdescent : baseEnd_2486028 < baseStart_2486028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486144 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_2486144 : Nat := 118140960795 + 2486144 * 2 ^ 59
def prefixEnd_2486144 : Nat := 4983230072969 + 3 ^ 40 * 2486144 * 2
def baseEnd_2486144 : Nat := 851057898861084122577625

theorem tailTrace_2486144 : CollatzResearch.WordTrace tailWord_2486144 prefixEnd_2486144 851057898861084122577625 := by
  unfold tailWord_2486144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45338560552566181218104743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60451414070088241624139657 45338560552566181218104743)
  ·
    refine ⟨68007840828849271827157115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45338560552566181218104743 68007840828849271827157115)
    ·
      refine ⟨102011761243273907740735673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68007840828849271827157115 102011761243273907740735673)
      ·
        refine ⟨76508820932455430805551755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102011761243273907740735673 76508820932455430805551755)
        ·
          refine ⟨114763231398683146208327633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76508820932455430805551755 114763231398683146208327633)
          ·
            refine ⟨86072423549012359656245725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114763231398683146208327633 86072423549012359656245725)
            ·
              refine ⟨32277158830879634871092147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86072423549012359656245725 32277158830879634871092147)
              ·
                refine ⟨48415738246319452306638221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32277158830879634871092147 48415738246319452306638221)
                ·
                  refine ⟨18155901842369794614989333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48415738246319452306638221 18155901842369794614989333)
                  ·
                    refine ⟨851057898861084122577625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18155901842369794614989333 851057898861084122577625)
                    ·
                      rfl

theorem cell22_2486144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_2486144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486144 prefixEnd_2486144 := by exact prefixLift 2486144
  have htrace : WordTrace (prefixWord ++ tailWord_2486144) baseStart_2486144 baseEnd_2486144 := by
    simpa [prefixWord, tailWord_2486144, baseEnd_2486144] using wordTrace_append hprefix tailTrace_2486144
  have hstable : (prefixWord ++ tailWord_2486144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486144).length < 2 ^ (prefixWord ++ tailWord_2486144).sum := by decide
  have hdescent : baseEnd_2486144 < baseStart_2486144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486197 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2486197 : Nat := 118140960795 + 2486197 * 2 ^ 59
def prefixEnd_2486197 : Nat := 4983230072969 + 3 ^ 40 * 2486197 * 2
def baseEnd_2486197 : Nat := 851076041844209651002463

theorem tailTrace_2486197 : CollatzResearch.WordTrace tailWord_2486197 prefixEnd_2486197 851076041844209651002463 := by
  unfold tailWord_2486197
  simp only [CollatzResearch.WordTrace]
  refine ⟨90679054173940352487888845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60452702782626901658592563 90679054173940352487888845)
  ·
    refine ⟨34004645315227632182958317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90679054173940352487888845 34004645315227632182958317)
    ·
      refine ⟨12751741993210362068609369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34004645315227632182958317 12751741993210362068609369)
      ·
        refine ⟨9563806494907771551457027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12751741993210362068609369 9563806494907771551457027)
        ·
          refine ⟨14345709742361657327185541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9563806494907771551457027 14345709742361657327185541)
          ·
            refine ⟨2689820576692810748847289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14345709742361657327185541 2689820576692810748847289)
            ·
              refine ⟨2017365432519608061635467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689820576692810748847289 2017365432519608061635467)
              ·
                refine ⟨3026048148779412092453201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017365432519608061635467 3026048148779412092453201)
                ·
                  refine ⟨2269536111584559069339901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026048148779412092453201 2269536111584559069339901)
                  ·
                    refine ⟨851076041844209651002463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269536111584559069339901 851076041844209651002463)
                    ·
                      rfl

theorem cell22_2486197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2486197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486197 prefixEnd_2486197 := by exact prefixLift 2486197
  have htrace : WordTrace (prefixWord ++ tailWord_2486197) baseStart_2486197 baseEnd_2486197 := by
    simpa [prefixWord, tailWord_2486197, baseEnd_2486197] using wordTrace_append hprefix tailTrace_2486197
  have hstable : (prefixWord ++ tailWord_2486197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486197).length < 2 ^ (prefixWord ++ tailWord_2486197).sum := by decide
  have hdescent : baseEnd_2486197 < baseStart_2486197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486268 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2486268 : Nat := 118140960795 + 2486268 * 2 ^ 59
def prefixEnd_2486268 : Nat := 4983230072969 + 3 ^ 40 * 2486268 * 2
def baseEnd_2486268 : Nat := 851100346595189132477245

theorem tailTrace_2486268 : CollatzResearch.WordTrace tailWord_2486268 prefixEnd_2486268 851100346595189132477245 := by
  unfold tailWord_2486268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45340821878341565806861729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60454429171122087742482305 45340821878341565806861729)
  ·
    refine ⟨34005616408756174355146297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45340821878341565806861729 34005616408756174355146297)
    ·
      refine ⟨25504212306567130766359723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34005616408756174355146297 25504212306567130766359723)
      ·
        refine ⟨38256318459850696149539585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25504212306567130766359723 38256318459850696149539585)
        ·
          refine ⟨28692238844888022112154689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38256318459850696149539585 28692238844888022112154689)
          ·
            refine ⟨21519179133666016584116017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28692238844888022112154689 21519179133666016584116017)
            ·
              refine ⟨16139384350249512438087013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21519179133666016584116017 16139384350249512438087013)
              ·
                refine ⟨3026134565671783582141315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16139384350249512438087013 3026134565671783582141315)
                ·
                  refine ⟨4539201848507675373211973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026134565671783582141315 4539201848507675373211973)
                  ·
                    refine ⟨851100346595189132477245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539201848507675373211973 851100346595189132477245)
                    ·
                      rfl

theorem cell22_2486268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2486268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486268 prefixEnd_2486268 := by exact prefixLift 2486268
  have htrace : WordTrace (prefixWord ++ tailWord_2486268) baseStart_2486268 baseEnd_2486268 := by
    simpa [prefixWord, tailWord_2486268, baseEnd_2486268] using wordTrace_append hprefix tailTrace_2486268
  have hstable : (prefixWord ++ tailWord_2486268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486268).length < 2 ^ (prefixWord ++ tailWord_2486268).sum := by decide
  have hdescent : baseEnd_2486268 < baseStart_2486268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486300 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_2486300 : Nat := 118140960795 + 2486300 * 2 ^ 59
def prefixEnd_2486300 : Nat := 4983230072969 + 3 ^ 40 * 2486300 * 2
def baseEnd_2486300 : Nat := 283703766949717238559049

theorem tailTrace_2486300 : CollatzResearch.WordTrace tailWord_2486300 prefixEnd_2486300 283703766949717238559049 := by
  unfold tailWord_2486300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45341405446283600539444177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60455207261711467385925569 45341405446283600539444177)
  ·
    refine ⟨34006054084712700404583133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45341405446283600539444177 34006054084712700404583133)
    ·
      refine ⟨12752270281767262651718675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34006054084712700404583133 12752270281767262651718675)
      ·
        refine ⟨19128405422650893977578013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12752270281767262651718675 19128405422650893977578013)
        ·
          refine ⟨7173152033494085241591755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19128405422650893977578013 7173152033494085241591755)
          ·
            refine ⟨10759728050241127862387633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173152033494085241591755 10759728050241127862387633)
            ·
              refine ⟨8069796037680845896790725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10759728050241127862387633 8069796037680845896790725)
              ·
                refine ⟨1513086757065158605648261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8069796037680845896790725 1513086757065158605648261)
                ·
                  refine ⟨283703766949717238559049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513086757065158605648261 283703766949717238559049)
                  ·
                    rfl

theorem cell22_2486300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_2486300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486300 prefixEnd_2486300 := by exact prefixLift 2486300
  have htrace : WordTrace (prefixWord ++ tailWord_2486300) baseStart_2486300 baseEnd_2486300 := by
    simpa [prefixWord, tailWord_2486300, baseEnd_2486300] using wordTrace_append hprefix tailTrace_2486300
  have hstable : (prefixWord ++ tailWord_2486300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486300).length < 2 ^ (prefixWord ++ tailWord_2486300).sum := by decide
  have hdescent : baseEnd_2486300 < baseStart_2486300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486328 : List Nat := [2, 1, 2, 1, 6, 1, 1, 8]
def baseStart_2486328 : Nat := 118140960795 + 2486328 * 2 ^ 59
def prefixEnd_2486328 : Nat := 4983230072969 + 3 ^ 40 * 2486328 * 2
def baseEnd_2486328 : Nat := 94568987313485441775229

theorem tailTrace_2486328 : CollatzResearch.WordTrace tailWord_2486328 prefixEnd_2486328 94568987313485441775229 := by
  unfold tailWord_2486328
  simp only [CollatzResearch.WordTrace]
  refine ⟨45341916068232880930453819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60455888090977174573938425 45341916068232880930453819)
  ·
    refine ⟨68012874102349321395680729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45341916068232880930453819 68012874102349321395680729)
    ·
      refine ⟨51009655576761991046760547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68012874102349321395680729 51009655576761991046760547)
      ·
        refine ⟨76514483365142986570140821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51009655576761991046760547 76514483365142986570140821)
        ·
          refine ⟨3586616407741077495475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76514483365142986570140821 3586616407741077495475351)
          ·
            refine ⟨5379924611611616243213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586616407741077495475351 5379924611611616243213027)
            ·
              refine ⟨8069886917417424364819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379924611611616243213027 8069886917417424364819541)
              ·
                refine ⟨94568987313485441775229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8069886917417424364819541 94568987313485441775229)
                ·
                  rfl

theorem cell22_2486328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_2486328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486328 prefixEnd_2486328 := by exact prefixLift 2486328
  have htrace : WordTrace (prefixWord ++ tailWord_2486328) baseStart_2486328 baseEnd_2486328 := by
    simpa [prefixWord, tailWord_2486328, baseEnd_2486328] using wordTrace_append hprefix tailTrace_2486328
  have hstable : (prefixWord ++ tailWord_2486328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486328).length < 2 ^ (prefixWord ++ tailWord_2486328).sum := by decide
  have hdescent : baseEnd_2486328 < baseStart_2486328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486334 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2486334 : Nat := 118140960795 + 2486334 * 2 ^ 59
def prefixEnd_2486334 : Nat := 4983230072969 + 3 ^ 40 * 2486334 * 2
def baseEnd_2486334 : Nat := 283707646581328986775681

theorem tailTrace_2486334 : CollatzResearch.WordTrace tailWord_2486334 prefixEnd_2486334 283707646581328986775681 := by
  unfold tailWord_2486334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11335506371805503110703257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60456033982962683257084037 11335506371805503110703257)
  ·
    refine ⟨8501629778854127333027443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11335506371805503110703257 8501629778854127333027443)
    ·
      refine ⟨12752444668281190999541165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8501629778854127333027443 12752444668281190999541165)
      ·
        refine ⟨4782166750605446624827937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12752444668281190999541165 4782166750605446624827937)
        ·
          refine ⟨3586625062954084968620953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782166750605446624827937 3586625062954084968620953)
          ·
            refine ⟨2689968797215563726465715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586625062954084968620953 2689968797215563726465715)
            ·
              refine ⟨4034953195823345589698573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689968797215563726465715 4034953195823345589698573)
              ·
                refine ⟨1513107448433754596136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4034953195823345589698573 1513107448433754596136965)
                ·
                  refine ⟨283707646581328986775681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513107448433754596136965 283707646581328986775681)
                  ·
                    rfl

theorem cell22_2486334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2486334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486334 prefixEnd_2486334 := by exact prefixLift 2486334
  have htrace : WordTrace (prefixWord ++ tailWord_2486334) baseStart_2486334 baseEnd_2486334 := by
    simpa [prefixWord, tailWord_2486334, baseEnd_2486334] using wordTrace_append hprefix tailTrace_2486334
  have hstable : (prefixWord ++ tailWord_2486334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486334).length < 2 ^ (prefixWord ++ tailWord_2486334).sum := by decide
  have hdescent : baseEnd_2486334 < baseStart_2486334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486341 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2486341 : Nat := 118140960795 + 2486341 * 2 ^ 59
def prefixEnd_2486341 : Nat := 4983230072969 + 3 ^ 40 * 2486341 * 2
def baseEnd_2486341 : Nat := 851125335987041275402021

theorem tailTrace_2486341 : CollatzResearch.WordTrace tailWord_2486341 prefixEnd_2486341 851125335987041275402021 := by
  unfold tailWord_2486341
  simp only [CollatzResearch.WordTrace]
  refine ⟨90684306285418665081130877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60456204190279110054087251 90684306285418665081130877)
  ·
    refine ⟨34006614857031999405424079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90684306285418665081130877 34006614857031999405424079)
    ·
      refine ⟨51009922285547999108136119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34006614857031999405424079 51009922285547999108136119)
      ·
        refine ⟨76514883428321998662204179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51009922285547999108136119 76514883428321998662204179)
        ·
          refine ⟨114772325142482997993306269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76514883428321998662204179 114772325142482997993306269)
          ·
            refine ⟨43039621928431124247489851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114772325142482997993306269 43039621928431124247489851)
            ·
              refine ⟨64559432892646686371234777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43039621928431124247489851 64559432892646686371234777)
              ·
                refine ⟨48419574669485014778426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64559432892646686371234777 48419574669485014778426083)
                ·
                  refine ⟨72629362004227522167639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48419574669485014778426083 72629362004227522167639125)
                  ·
                    refine ⟨851125335987041275402021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72629362004227522167639125 851125335987041275402021)
                    ·
                      rfl

theorem cell22_2486341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2486341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486341 prefixEnd_2486341 := by exact prefixLift 2486341
  have htrace : WordTrace (prefixWord ++ tailWord_2486341) baseStart_2486341 baseEnd_2486341 := by
    simpa [prefixWord, tailWord_2486341, baseEnd_2486341] using wordTrace_append hprefix tailTrace_2486341
  have hstable : (prefixWord ++ tailWord_2486341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486341).length < 2 ^ (prefixWord ++ tailWord_2486341).sum := by decide
  have hdescent : baseEnd_2486341 < baseStart_2486341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486360 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_2486360 : Nat := 118140960795 + 2486360 * 2 ^ 59
def prefixEnd_2486360 : Nat := 4983230072969 + 3 ^ 40 * 2486360 * 2
def baseEnd_2486360 : Nat := 851131840075331559176963

theorem tailTrace_2486360 : CollatzResearch.WordTrace tailWord_2486360 prefixEnd_2486360 851131840075331559176963 := by
  unfold tailWord_2486360
  simp only [CollatzResearch.WordTrace]
  refine ⟨45342499636174915663036267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60456666181566554217381689 45342499636174915663036267)
  ·
    refine ⟨68013749454262373494554401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45342499636174915663036267 68013749454262373494554401)
    ·
      refine ⟨51010312090696780120915801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68013749454262373494554401 51010312090696780120915801)
      ·
        refine ⟨38257734068022585090686851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51010312090696780120915801 38257734068022585090686851)
        ·
          refine ⟨57386601102033877636030277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38257734068022585090686851 57386601102033877636030277)
          ·
            refine ⟨10759987706631352056755677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57386601102033877636030277 10759987706631352056755677)
            ·
              refine ⟨4034995389986757021283379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10759987706631352056755677 4034995389986757021283379)
              ·
                refine ⟨6052493084980135531925069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034995389986757021283379 6052493084980135531925069)
                ·
                  refine ⟨2269684906867550824471901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6052493084980135531925069 2269684906867550824471901)
                  ·
                    refine ⟨851131840075331559176963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269684906867550824471901 851131840075331559176963)
                    ·
                      rfl

theorem cell22_2486360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_2486360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486360 prefixEnd_2486360 := by exact prefixLift 2486360
  have htrace : WordTrace (prefixWord ++ tailWord_2486360) baseStart_2486360 baseEnd_2486360 := by
    simpa [prefixWord, tailWord_2486360, baseEnd_2486360] using wordTrace_append hprefix tailTrace_2486360
  have hstable : (prefixWord ++ tailWord_2486360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486360).length < 2 ^ (prefixWord ++ tailWord_2486360).sum := by decide
  have hdescent : baseEnd_2486360 < baseStart_2486360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486366 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2486366 : Nat := 118140960795 + 2486366 * 2 ^ 59
def prefixEnd_2486366 : Nat := 4983230072969 + 3 ^ 40 * 2486366 * 2
def baseEnd_2486366 : Nat := 851133893997949543526945

theorem tailTrace_2486366 : CollatzResearch.WordTrace tailWord_2486366 prefixEnd_2486366 851133893997949543526945 := by
  unfold tailWord_2486366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11335652263791011793848869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60456812073552062900527301 11335652263791011793848869)
  ·
    refine ⟨2125434799460814711346663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11335652263791011793848869 2125434799460814711346663)
    ·
      refine ⟨3188152199191222067019995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125434799460814711346663 3188152199191222067019995)
      ·
        refine ⟨4782228298786833100529993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188152199191222067019995 4782228298786833100529993)
        ·
          refine ⟨3586671224090124825397495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782228298786833100529993 3586671224090124825397495)
          ·
            refine ⟨5380006836135187238096243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586671224090124825397495 5380006836135187238096243)
            ·
              refine ⟨8070010254202780857144365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380006836135187238096243 8070010254202780857144365)
              ·
                refine ⟨3026253845326042821429137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8070010254202780857144365 3026253845326042821429137)
                ·
                  refine ⟨2269690383994532116071853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026253845326042821429137 2269690383994532116071853)
                  ·
                    refine ⟨851133893997949543526945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269690383994532116071853 851133893997949543526945)
                    ·
                      rfl

theorem cell22_2486366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2486366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486366 prefixEnd_2486366 := by exact prefixLift 2486366
  have htrace : WordTrace (prefixWord ++ tailWord_2486366) baseStart_2486366 baseEnd_2486366 := by
    simpa [prefixWord, tailWord_2486366, baseEnd_2486366] using wordTrace_append hprefix tailTrace_2486366
  have hstable : (prefixWord ++ tailWord_2486366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486366).length < 2 ^ (prefixWord ++ tailWord_2486366).sum := by decide
  have hdescent : baseEnd_2486366 < baseStart_2486366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486450 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_2486450 : Nat := 118140960795 + 2486450 * 2 ^ 59
def prefixEnd_2486450 : Nat := 4983230072969 + 3 ^ 40 * 2486450 * 2
def baseEnd_2486450 : Nat := 851162648914601324426687

theorem tailTrace_2486450 : CollatzResearch.WordTrace tailWord_2486450 prefixEnd_2486450 851162648914601324426687 := by
  unfold tailWord_2486450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672070460505944174212201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60458854561349184464565869 22672070460505944174212201)
  ·
    refine ⟨17004052845379458130659151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22672070460505944174212201 17004052845379458130659151)
    ·
      refine ⟨25506079268069187195988727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17004052845379458130659151 25506079268069187195988727)
      ·
        refine ⟨38259118902103780793983091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25506079268069187195988727 38259118902103780793983091)
        ·
          refine ⟨57388678353155671190974637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38259118902103780793983091 57388678353155671190974637)
          ·
            refine ⟨21520754382433376696615489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57388678353155671190974637 21520754382433376696615489)
            ·
              refine ⟨16140565786825032522461617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21520754382433376696615489 16140565786825032522461617)
              ·
                refine ⟨12105424340118774391846213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16140565786825032522461617 12105424340118774391846213)
                ·
                  refine ⟨2269767063772270198471165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12105424340118774391846213 2269767063772270198471165)
                  ·
                    refine ⟨851162648914601324426687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269767063772270198471165 851162648914601324426687)
                    ·
                      rfl

theorem cell22_2486450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_2486450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486450 prefixEnd_2486450 := by exact prefixLift 2486450
  have htrace : WordTrace (prefixWord ++ tailWord_2486450) baseStart_2486450 baseEnd_2486450 := by
    simpa [prefixWord, tailWord_2486450, baseEnd_2486450] using wordTrace_append hprefix tailTrace_2486450
  have hstable : (prefixWord ++ tailWord_2486450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486450).length < 2 ^ (prefixWord ++ tailWord_2486450).sum := by decide
  have hdescent : baseEnd_2486450 < baseStart_2486450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486508 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_2486508 : Nat := 118140960795 + 2486508 * 2 ^ 59
def prefixEnd_2486508 : Nat := 4983230072969 + 3 ^ 40 * 2486508 * 2
def baseEnd_2486508 : Nat := 283727501166636168825503

theorem tailTrace_2486508 : CollatzResearch.WordTrace tailWord_2486508 prefixEnd_2486508 283727501166636168825503 := by
  unfold tailWord_2486508
  simp only [CollatzResearch.WordTrace]
  refine ⟨45345198637906826301230089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60460264850542435068306785 45345198637906826301230089)
  ·
    refine ⟨34008898978430119725922567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45345198637906826301230089 34008898978430119725922567)
    ·
      refine ⟨51013348467645179588883851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34008898978430119725922567 51013348467645179588883851)
      ·
        refine ⟨76520022701467769383325777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51013348467645179588883851 76520022701467769383325777)
        ·
          refine ⟨57390017026100827037494333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76520022701467769383325777 57390017026100827037494333)
          ·
            refine ⟨21521256384787810139060375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57390017026100827037494333 21521256384787810139060375)
            ·
              refine ⟨32281884577181715208590563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21521256384787810139060375 32281884577181715208590563)
              ·
                refine ⟨48422826865772572812885845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32281884577181715208590563 48422826865772572812885845)
                ·
                  refine ⟨283727501166636168825503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48422826865772572812885845 283727501166636168825503)
                  ·
                    rfl

theorem cell22_2486508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_2486508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486508 prefixEnd_2486508 := by exact prefixLift 2486508
  have htrace : WordTrace (prefixWord ++ tailWord_2486508) baseStart_2486508 baseEnd_2486508 := by
    simpa [prefixWord, tailWord_2486508, baseEnd_2486508] using wordTrace_append hprefix tailTrace_2486508
  have hstable : (prefixWord ++ tailWord_2486508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486508).length < 2 ^ (prefixWord ++ tailWord_2486508).sum := by decide
  have hdescent : baseEnd_2486508 < baseStart_2486508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486600 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2486600 : Nat := 118140960795 + 2486600 * 2 ^ 59
def prefixEnd_2486600 : Nat := 4983230072969 + 3 ^ 40 * 2486600 * 2
def baseEnd_2486600 : Nat := 851213996980050933176227

theorem tailTrace_2486600 : CollatzResearch.WordTrace tailWord_2486600 prefixEnd_2486600 851213996980050933176227 := by
  unfold tailWord_2486600
  simp only [CollatzResearch.WordTrace]
  refine ⟨45346876395740176157404627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60462501860986901543206169 45346876395740176157404627)
  ·
    refine ⟨68020314593610264236106941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45346876395740176157404627 68020314593610264236106941)
    ·
      refine ⟨25507617972603849088540103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68020314593610264236106941 25507617972603849088540103)
      ·
        refine ⟨38261426958905773632810155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25507617972603849088540103 38261426958905773632810155)
        ·
          refine ⟨57392140438358660449215233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38261426958905773632810155 57392140438358660449215233)
          ·
            refine ⟨43044105328768995336911425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57392140438358660449215233 43044105328768995336911425)
            ·
              refine ⟨32283078996576746502683569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43044105328768995336911425 32283078996576746502683569)
              ·
                refine ⟨24212309247432559877012677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32283078996576746502683569 24212309247432559877012677)
                ·
                  refine ⟨4539807983893604976939877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24212309247432559877012677 4539807983893604976939877)
                  ·
                    refine ⟨851213996980050933176227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539807983893604976939877 851213996980050933176227)
                    ·
                      rfl

theorem cell22_2486600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2486600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486600 prefixEnd_2486600 := by exact prefixLift 2486600
  have htrace : WordTrace (prefixWord ++ tailWord_2486600) baseStart_2486600 baseEnd_2486600 := by
    simpa [prefixWord, tailWord_2486600, baseEnd_2486600] using wordTrace_append hprefix tailTrace_2486600
  have hstable : (prefixWord ++ tailWord_2486600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486600).length < 2 ^ (prefixWord ++ tailWord_2486600).sum := by decide
  have hdescent : baseEnd_2486600 < baseStart_2486600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486636 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_2486636 : Nat := 118140960795 + 2486636 * 2 ^ 59
def prefixEnd_2486636 : Nat := 4983230072969 + 3 ^ 40 * 2486636 * 2
def baseEnd_2486636 : Nat := 851226320515758839276117

theorem tailTrace_2486636 : CollatzResearch.WordTrace tailWord_2486636 prefixEnd_2486636 851226320515758839276117 := by
  unfold tailWord_2486636
  simp only [CollatzResearch.WordTrace]
  refine ⟨45347532909674965231559881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60463377212899953642079841 45347532909674965231559881)
  ·
    refine ⟨34010649682256223923669911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45347532909674965231559881 34010649682256223923669911)
    ·
      refine ⟨51015974523384335885504867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34010649682256223923669911 51015974523384335885504867)
      ·
        refine ⟨76523961785076503828257301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51015974523384335885504867 76523961785076503828257301)
        ·
          refine ⟨3587060708675461116949561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76523961785076503828257301 3587060708675461116949561)
          ·
            refine ⟨2690295531506595837712171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587060708675461116949561 2690295531506595837712171)
            ·
              refine ⟨4035443297259893756568257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690295531506595837712171 4035443297259893756568257)
              ·
                refine ⟨3026582472944920317426193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035443297259893756568257 3026582472944920317426193)
                ·
                  refine ⟨2269936854708690238069645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026582472944920317426193 2269936854708690238069645)
                  ·
                    refine ⟨851226320515758839276117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269936854708690238069645 851226320515758839276117)
                    ·
                      rfl

theorem cell22_2486636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_2486636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486636 prefixEnd_2486636 := by exact prefixLift 2486636
  have htrace : WordTrace (prefixWord ++ tailWord_2486636) baseStart_2486636 baseEnd_2486636 := by
    simpa [prefixWord, tailWord_2486636, baseEnd_2486636] using wordTrace_append hprefix tailTrace_2486636
  have hstable : (prefixWord ++ tailWord_2486636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486636).length < 2 ^ (prefixWord ++ tailWord_2486636).sum := by decide
  have hdescent : baseEnd_2486636 < baseStart_2486636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486666 : List Nat := [3, 1, 2, 5, 1, 2, 2, 6]
def baseStart_2486666 : Nat := 118140960795 + 2486666 * 2 ^ 59
def prefixEnd_2486666 : Nat := 4983230072969 + 3 ^ 40 * 2486666 * 2
def baseEnd_2486666 : Nat := 94581843347649862336225

theorem tailTrace_2486666 : CollatzResearch.WordTrace tailWord_2486666 prefixEnd_2486666 94581843347649862336225 := by
  unfold tailWord_2486666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674040002310311396677963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60464106672827497057807901 22674040002310311396677963)
  ·
    refine ⟨34011060003465467095016945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22674040002310311396677963 34011060003465467095016945)
    ·
      refine ⟨25508295002599100321262709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34011060003465467095016945 25508295002599100321262709)
      ·
        refine ⟨2391402656493665655118379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25508295002599100321262709 2391402656493665655118379)
        ·
          refine ⟨3587103984740498482677569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391402656493665655118379 3587103984740498482677569)
          ·
            refine ⟨2690327988555373862008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587103984740498482677569 2690327988555373862008177)
            ·
              refine ⟨2017745991416530396506133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690327988555373862008177 2017745991416530396506133)
              ·
                refine ⟨94581843347649862336225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2017745991416530396506133 94581843347649862336225)
                ·
                  rfl

theorem cell22_2486666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_2486666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486666 prefixEnd_2486666 := by exact prefixLift 2486666
  have htrace : WordTrace (prefixWord ++ tailWord_2486666) baseStart_2486666 baseEnd_2486666 := by
    simpa [prefixWord, tailWord_2486666, baseEnd_2486666] using wordTrace_append hprefix tailTrace_2486666
  have hstable : (prefixWord ++ tailWord_2486666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486666).length < 2 ^ (prefixWord ++ tailWord_2486666).sum := by decide
  have hdescent : baseEnd_2486666 < baseStart_2486666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486737 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_2486737 : Nat := 118140960795 + 2486737 * 2 ^ 59
def prefixEnd_2486737 : Nat := 4983230072969 + 3 ^ 40 * 2486737 * 2
def baseEnd_2486737 : Nat := 851260894879828242500807

theorem tailTrace_2486737 : CollatzResearch.WordTrace tailWord_2486737 prefixEnd_2486737 851260894879828242500807 := by
  unfold tailWord_2486737
  simp only [CollatzResearch.WordTrace]
  refine ⟨90698749591984024712546465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60465833061322683141697643 90698749591984024712546465)
  ·
    refine ⟨68024062193988018534409849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90698749591984024712546465 68024062193988018534409849)
    ·
      refine ⟨51018046645491013900807387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68024062193988018534409849 51018046645491013900807387)
      ·
        refine ⟨76527069968236520851211081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51018046645491013900807387 76527069968236520851211081)
        ·
          refine ⟨57395302476177390638408311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76527069968236520851211081 57395302476177390638408311)
          ·
            refine ⟨86092953714266085957612467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57395302476177390638408311 86092953714266085957612467)
            ·
              refine ⟨129139430571399128936418701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86092953714266085957612467 129139430571399128936418701)
              ·
                refine ⟨48427286464274673351157013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129139430571399128936418701 48427286464274673351157013)
                ·
                  refine ⟨2270029053012875313335485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48427286464274673351157013 2270029053012875313335485)
                  ·
                    refine ⟨851260894879828242500807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2270029053012875313335485 851260894879828242500807)
                    ·
                      rfl

theorem cell22_2486737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_2486737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486737 prefixEnd_2486737 := by exact prefixLift 2486737
  have htrace : WordTrace (prefixWord ++ tailWord_2486737) baseStart_2486737 baseEnd_2486737 := by
    simpa [prefixWord, tailWord_2486737, baseEnd_2486737] using wordTrace_append hprefix tailTrace_2486737
  have hstable : (prefixWord ++ tailWord_2486737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486737).length < 2 ^ (prefixWord ++ tailWord_2486737).sum := by decide
  have hdescent : baseEnd_2486737 < baseStart_2486737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486741 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2486741 : Nat := 118140960795 + 2486741 * 2 ^ 59
def prefixEnd_2486741 : Nat := 4983230072969 + 3 ^ 40 * 2486741 * 2
def baseEnd_2486741 : Nat := 851262264161573565400795

theorem tailTrace_2486741 : CollatzResearch.WordTrace tailWord_2486741 prefixEnd_2486741 851262264161573565400795 := by
  unfold tailWord_2486741
  simp only [CollatzResearch.WordTrace]
  refine ⟨90698895483969533395692077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60465930322646355597128051 90698895483969533395692077)
  ·
    refine ⟨34012085806488575023384529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90698895483969533395692077 34012085806488575023384529)
    ·
      refine ⟨25509064354866431267538397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34012085806488575023384529 25509064354866431267538397)
      ·
        refine ⟨9565899133074911725326899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25509064354866431267538397 9565899133074911725326899)
        ·
          refine ⟨14348848699612367587990349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9565899133074911725326899 14348848699612367587990349)
          ·
            refine ⟨5380818262354637845496381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14348848699612367587990349 5380818262354637845496381)
            ·
              refine ⟨2017806848382989192061143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5380818262354637845496381 2017806848382989192061143)
              ·
                refine ⟨3026710272574483788091715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017806848382989192061143 3026710272574483788091715)
                ·
                  refine ⟨4540065408861725682137573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026710272574483788091715 4540065408861725682137573)
                  ·
                    refine ⟨851262264161573565400795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540065408861725682137573 851262264161573565400795)
                    ·
                      rfl

theorem cell22_2486741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2486741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486741 prefixEnd_2486741 := by exact prefixLift 2486741
  have htrace : WordTrace (prefixWord ++ tailWord_2486741) baseStart_2486741 baseEnd_2486741 := by
    simpa [prefixWord, tailWord_2486741, baseEnd_2486741] using wordTrace_append hprefix tailTrace_2486741
  have hstable : (prefixWord ++ tailWord_2486741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486741).length < 2 ^ (prefixWord ++ tailWord_2486741).sum := by decide
  have hdescent : baseEnd_2486741 < baseStart_2486741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486752 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_2486752 : Nat := 118140960795 + 2486752 * 2 ^ 59
def prefixEnd_2486752 : Nat := 4983230072969 + 3 ^ 40 * 2486752 * 2
def baseEnd_2486752 : Nat := 851266029686373203375761

theorem tailTrace_2486752 : CollatzResearch.WordTrace tailWord_2486752 prefixEnd_2486752 851266029686373203375761 := by
  unfold tailWord_2486752
  simp only [CollatzResearch.WordTrace]
  refine ⟨45349648343464841137171255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60466197791286454849561673 45349648343464841137171255)
  ·
    refine ⟨68024472515197261705756883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45349648343464841137171255 68024472515197261705756883)
    ·
      refine ⟨102036708772795892558635325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68024472515197261705756883 102036708772795892558635325)
      ·
        refine ⟨38263765789798459709488247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102036708772795892558635325 38263765789798459709488247)
        ·
          refine ⟨57395648684697689564232371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38263765789798459709488247 57395648684697689564232371)
          ·
            refine ⟨86093473027046534346348557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57395648684697689564232371 86093473027046534346348557)
            ·
              refine ⟨32285052385142450379880709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86093473027046534346348557 32285052385142450379880709)
              ·
                refine ⟨6053447322214209446227633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32285052385142450379880709 6053447322214209446227633)
                ·
                  refine ⟨4540085491660657084670725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6053447322214209446227633 4540085491660657084670725)
                  ·
                    refine ⟨851266029686373203375761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540085491660657084670725 851266029686373203375761)
                    ·
                      rfl

theorem cell22_2486752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_2486752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486752 prefixEnd_2486752 := by exact prefixLift 2486752
  have htrace : WordTrace (prefixWord ++ tailWord_2486752) baseStart_2486752 baseEnd_2486752 := by
    simpa [prefixWord, tailWord_2486752, baseEnd_2486752] using wordTrace_append hprefix tailTrace_2486752
  have hstable : (prefixWord ++ tailWord_2486752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486752).length < 2 ^ (prefixWord ++ tailWord_2486752).sum := by decide
  have hdescent : baseEnd_2486752 < baseStart_2486752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486786 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2486786 : Nat := 118140960795 + 2486786 * 2 ^ 59
def prefixEnd_2486786 : Nat := 4983230072969 + 3 ^ 40 * 2486786 * 2
def baseEnd_2486786 : Nat := 851277668581208448025657

theorem tailTrace_2486786 : CollatzResearch.WordTrace tailWord_2486786 prefixEnd_2486786 851277668581208448025657 := by
  unfold tailWord_2486786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22675134192201626520270053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60467024512537670720720141 22675134192201626520270053)
  ·
    refine ⟨4251587661037804972550635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22675134192201626520270053 4251587661037804972550635)
    ·
      refine ⟨6377381491556707458825953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4251587661037804972550635 6377381491556707458825953)
      ·
        refine ⟨4783036118667530594119465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6377381491556707458825953 4783036118667530594119465)
        ·
          refine ⟨3587277089000647945589599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4783036118667530594119465 3587277089000647945589599)
          ·
            refine ⟨5380915633500971918384399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587277089000647945589599 5380915633500971918384399)
            ·
              refine ⟨8071373450251457877576599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380915633500971918384399 8071373450251457877576599)
              ·
                refine ⟨12107060175377186816364899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8071373450251457877576599 12107060175377186816364899)
                ·
                  refine ⟨18160590263065780224547349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107060175377186816364899 18160590263065780224547349)
                  ·
                    refine ⟨851277668581208448025657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18160590263065780224547349 851277668581208448025657)
                    ·
                      rfl

theorem cell22_2486786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2486786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486786 prefixEnd_2486786 := by exact prefixLift 2486786
  have htrace : WordTrace (prefixWord ++ tailWord_2486786) baseStart_2486786 baseEnd_2486786 := by
    simpa [prefixWord, tailWord_2486786, baseEnd_2486786] using wordTrace_append hprefix tailTrace_2486786
  have hstable : (prefixWord ++ tailWord_2486786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486786).length < 2 ^ (prefixWord ++ tailWord_2486786).sum := by decide
  have hdescent : baseEnd_2486786 < baseStart_2486786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486790 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2486790 : Nat := 118140960795 + 2486790 * 2 ^ 59
def prefixEnd_2486790 : Nat := 4983230072969 + 3 ^ 40 * 2486790 * 2
def baseEnd_2486790 : Nat := 283759679287651256975215

theorem tailTrace_2486790 : CollatzResearch.WordTrace tailWord_2486790 prefixEnd_2486790 283759679287651256975215 := by
  unfold tailWord_2486790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834396333149750461382057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60467121773861343176150549 2834396333149750461382057)
  ·
    refine ⟨2125797249862312846036543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2834396333149750461382057 2125797249862312846036543)
    ·
      refine ⟨3188695874793469269054815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125797249862312846036543 3188695874793469269054815)
      ·
        refine ⟨4783043812190203903582223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188695874793469269054815 4783043812190203903582223)
        ·
          refine ⟨7174565718285305855373335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783043812190203903582223 7174565718285305855373335)
          ·
            refine ⟨10761848577427958783060003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174565718285305855373335 10761848577427958783060003)
            ·
              refine ⟨16142772866141938174590005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10761848577427958783060003 16142772866141938174590005)
              ·
                refine ⟨1513384956200806703867813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16142772866141938174590005 1513384956200806703867813)
                ·
                  refine ⟨283759679287651256975215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513384956200806703867813 283759679287651256975215)
                  ·
                    rfl

theorem cell22_2486790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2486790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486790 prefixEnd_2486790 := by exact prefixLift 2486790
  have htrace : WordTrace (prefixWord ++ tailWord_2486790) baseStart_2486790 baseEnd_2486790 := by
    simpa [prefixWord, tailWord_2486790, baseEnd_2486790] using wordTrace_append hprefix tailTrace_2486790
  have hstable : (prefixWord ++ tailWord_2486790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486790).length < 2 ^ (prefixWord ++ tailWord_2486790).sum := by decide
  have hdescent : baseEnd_2486790 < baseStart_2486790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486859 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 1, 4]
def baseStart_2486859 : Nat := 118140960795 + 2486859 * 2 ^ 59
def prefixEnd_2486859 : Nat := 4983230072969 + 3 ^ 40 * 2486859 * 2
def baseEnd_2486859 : Nat := 851302657973060590950433

theorem tailTrace_2486859 : CollatzResearch.WordTrace tailWord_2486859 prefixEnd_2486859 851302657973060590950433 := by
  unfold tailWord_2486859
  simp only [CollatzResearch.WordTrace]
  refine ⟨90703199297542039548487631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60468799531694693032325087 90703199297542039548487631)
  ·
    refine ⟨136054798946313059322731447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90703199297542039548487631 136054798946313059322731447)
    ·
      refine ⟨204082198419469588984097171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136054798946313059322731447 204082198419469588984097171)
      ·
        refine ⟨306123297629204383476145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204082198419469588984097171 306123297629204383476145757)
        ·
          refine ⟨114796236610951643803554659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306123297629204383476145757 114796236610951643803554659)
          ·
            refine ⟨172194354916427465705331989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114796236610951643803554659 172194354916427465705331989)
            ·
              refine ⟨8071610386707537454937437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172194354916427465705331989 8071610386707537454937437)
              ·
                refine ⟨3026853895015326545601539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8071610386707537454937437 3026853895015326545601539)
                ·
                  refine ⟨4540280842522989818402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026853895015326545601539 4540280842522989818402309)
                  ·
                    refine ⟨851302657973060590950433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540280842522989818402309 851302657973060590950433)
                    ·
                      rfl

theorem cell22_2486859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_2486859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486859 prefixEnd_2486859 := by exact prefixLift 2486859
  have htrace : WordTrace (prefixWord ++ tailWord_2486859) baseStart_2486859 baseEnd_2486859 := by
    simpa [prefixWord, tailWord_2486859, baseEnd_2486859] using wordTrace_append hprefix tailTrace_2486859
  have hstable : (prefixWord ++ tailWord_2486859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486859).length < 2 ^ (prefixWord ++ tailWord_2486859).sum := by decide
  have hdescent : baseEnd_2486859 < baseStart_2486859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486893 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2486893 : Nat := 118140960795 + 2486893 * 2 ^ 59
def prefixEnd_2486893 : Nat := 4983230072969 + 3 ^ 40 * 2486893 * 2
def baseEnd_2486893 : Nat := 851314296867895835600329

theorem tailTrace_2486893 : CollatzResearch.WordTrace tailWord_2486893 prefixEnd_2486893 851314296867895835600329 := by
  unfold tailWord_2486893
  simp only [CollatzResearch.WordTrace]
  refine ⟨90704439379418863355225333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60469626252945908903483555 90704439379418863355225333)
  ·
    refine ⟨8503541191820518439552375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90704439379418863355225333 8503541191820518439552375)
    ·
      refine ⟨12755311787730777659328563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8503541191820518439552375 12755311787730777659328563)
      ·
        refine ⟨19132967681596166488992845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12755311787730777659328563 19132967681596166488992845)
        ·
          refine ⟨7174862880598562433372317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19132967681596166488992845 7174862880598562433372317)
          ·
            refine ⟨2690573580224460912514619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7174862880598562433372317 2690573580224460912514619)
            ·
              refine ⟨4035860370336691368771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690573580224460912514619 4035860370336691368771929)
              ·
                refine ⟨3026895277752518526578947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035860370336691368771929 3026895277752518526578947)
                ·
                  refine ⟨4540342916628777789868421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026895277752518526578947 4540342916628777789868421)
                  ·
                    refine ⟨851314296867895835600329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540342916628777789868421 851314296867895835600329)
                    ·
                      rfl

theorem cell22_2486893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2486893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2486893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2486893 prefixEnd_2486893 := by exact prefixLift 2486893
  have htrace : WordTrace (prefixWord ++ tailWord_2486893) baseStart_2486893 baseEnd_2486893 := by
    simpa [prefixWord, tailWord_2486893, baseEnd_2486893] using wordTrace_append hprefix tailTrace_2486893
  have hstable : (prefixWord ++ tailWord_2486893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486893).length < 2 ^ (prefixWord ++ tailWord_2486893).sum := by decide
  have hdescent : baseEnd_2486893 < baseStart_2486893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487024 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_2487024 : Nat := 118140960795 + 2487024 * 2 ^ 59
def prefixEnd_2487024 : Nat := 4983230072969 + 3 ^ 40 * 2487024 * 2
def baseEnd_2487024 : Nat := 851359140845055160574927

theorem tailTrace_2487024 : CollatzResearch.WordTrace tailWord_2487024 prefixEnd_2487024 851359140845055160574927 := by
  unfold tailWord_2487024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45354608670972136364122063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60472811561296181818829417 45354608670972136364122063)
  ·
    refine ⟨68031913006458204546183095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45354608670972136364122063 68031913006458204546183095)
    ·
      refine ⟨102047869509687306819274643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68031913006458204546183095 102047869509687306819274643)
      ·
        refine ⟨153071804264530960228911965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102047869509687306819274643 153071804264530960228911965)
        ·
          refine ⟨57401926599199110085841987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153071804264530960228911965 57401926599199110085841987)
          ·
            refine ⟨86102889898798665128762981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57401926599199110085841987 86102889898798665128762981)
            ·
              refine ⟨16144291856024749711643059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86102889898798665128762981 16144291856024749711643059)
              ·
                refine ⟨24216437784037124567464589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16144291856024749711643059 24216437784037124567464589)
                ·
                  refine ⟨9081164169013921712799221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24216437784037124567464589 9081164169013921712799221)
                  ·
                    refine ⟨851359140845055160574927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9081164169013921712799221 851359140845055160574927)
                    ·
                      rfl

theorem cell22_2487024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_2487024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487024 prefixEnd_2487024 := by exact prefixLift 2487024
  have htrace : WordTrace (prefixWord ++ tailWord_2487024) baseStart_2487024 baseEnd_2487024 := by
    simpa [prefixWord, tailWord_2487024, baseEnd_2487024] using wordTrace_append hprefix tailTrace_2487024
  have hstable : (prefixWord ++ tailWord_2487024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487024).length < 2 ^ (prefixWord ++ tailWord_2487024).sum := by decide
  have hdescent : baseEnd_2487024 < baseStart_2487024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487092 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2487092 : Nat := 118140960795 + 2487092 * 2 ^ 59
def prefixEnd_2487092 : Nat := 4983230072969 + 3 ^ 40 * 2487092 * 2
def baseEnd_2487092 : Nat := 851382418634725649874719

theorem tailTrace_2487092 : CollatzResearch.WordTrace tailWord_2487092 prefixEnd_2487092 851382418634725649874719 := by
  unfold tailWord_2487092
  simp only [CollatzResearch.WordTrace]
  refine ⟨45355848752848960170859765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60474465003798613561146353 45355848752848960170859765)
  ·
    refine ⟨4252110820579590016018103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45355848752848960170859765 4252110820579590016018103)
    ·
      refine ⟨6378166230869385024027155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252110820579590016018103 6378166230869385024027155)
      ·
        refine ⟨9567249346304077536040733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6378166230869385024027155 9567249346304077536040733)
        ·
          refine ⟨3587718504864029076015275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9567249346304077536040733 3587718504864029076015275)
          ·
            refine ⟨5381577757296043614022913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587718504864029076015275 5381577757296043614022913)
            ·
              refine ⟨4036183317972032710517185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5381577757296043614022913 4036183317972032710517185)
              ·
                refine ⟨3027137488479024532887889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036183317972032710517185 3027137488479024532887889)
                ·
                  refine ⟨2270353116359268399665917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3027137488479024532887889 2270353116359268399665917)
                  ·
                    refine ⟨851382418634725649874719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2270353116359268399665917 851382418634725649874719)
                    ·
                      rfl

theorem cell22_2487092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2487092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487092 prefixEnd_2487092 := by exact prefixLift 2487092
  have htrace : WordTrace (prefixWord ++ tailWord_2487092) baseStart_2487092 baseEnd_2487092 := by
    simpa [prefixWord, tailWord_2487092, baseEnd_2487092] using wordTrace_append hprefix tailTrace_2487092
  have hstable : (prefixWord ++ tailWord_2487092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487092).length < 2 ^ (prefixWord ++ tailWord_2487092).sum := by decide
  have hdescent : baseEnd_2487092 < baseStart_2487092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487094 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2487094 : Nat := 118140960795 + 2487094 * 2 ^ 59
def prefixEnd_2487094 : Nat := 4983230072969 + 3 ^ 40 * 2487094 * 2
def baseEnd_2487094 : Nat := 283794367758532770441571

theorem tailTrace_2487094 : CollatzResearch.WordTrace tailWord_2487094 prefixEnd_2487094 283794367758532770441571 := by
  unfold tailWord_2487094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669485653230667167705771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60474513634460449788861557 5669485653230667167705771)
  ·
    refine ⟨8504228479846000751558657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669485653230667167705771 8504228479846000751558657)
    ·
      refine ⟨6378171359884500563668993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8504228479846000751558657 6378171359884500563668993)
      ·
        refine ⟨4783628519913375422751745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6378171359884500563668993 4783628519913375422751745)
        ·
          refine ⟨3587721389935031567063809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4783628519913375422751745 3587721389935031567063809)
          ·
            refine ⟨2690791042451273675297857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587721389935031567063809 2690791042451273675297857)
            ·
              refine ⟨2018093281838455256473393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690791042451273675297857 2018093281838455256473393)
              ·
                refine ⟨1513569961378841442355045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018093281838455256473393 1513569961378841442355045)
                ·
                  refine ⟨283794367758532770441571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513569961378841442355045 283794367758532770441571)
                  ·
                    rfl

theorem cell22_2487094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2487094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487094 prefixEnd_2487094 := by exact prefixLift 2487094
  have htrace : WordTrace (prefixWord ++ tailWord_2487094) baseStart_2487094 baseEnd_2487094 := by
    simpa [prefixWord, tailWord_2487094, baseEnd_2487094] using wordTrace_append hprefix tailTrace_2487094
  have hstable : (prefixWord ++ tailWord_2487094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487094).length < 2 ^ (prefixWord ++ tailWord_2487094).sum := by decide
  have hdescent : baseEnd_2487094 < baseStart_2487094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487105 : List Nat := [1, 2, 5, 3, 1, 2, 1, 7]
def baseStart_2487105 : Nat := 118140960795 + 2487105 * 2 ^ 59
def prefixEnd_2487105 : Nat := 4983230072969 + 3 ^ 40 * 2487105 * 2
def baseEnd_2487105 : Nat := 94598540977821994366631

theorem tailTrace_2487105 : CollatzResearch.WordTrace tailWord_2487105 prefixEnd_2487105 94598540977821994366631 := by
  unfold tailWord_2487105
  simp only [CollatzResearch.WordTrace]
  refine ⟨90712171654650823561942769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60474781103100549041295179 90712171654650823561942769)
  ·
    refine ⟨68034128740988117671457077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90712171654650823561942769 68034128740988117671457077)
    ·
      refine ⟨6378199569467636031699101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68034128740988117671457077 6378199569467636031699101)
      ·
        refine ⟨2391824838550363511887163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6378199569467636031699101 2391824838550363511887163)
        ·
          refine ⟨3587737257825545267830745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391824838550363511887163 3587737257825545267830745)
          ·
            refine ⟨2690802943369158950873059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587737257825545267830745 2690802943369158950873059)
            ·
              refine ⟨4036204415053738426309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690802943369158950873059 4036204415053738426309589)
              ·
                refine ⟨94598540977821994366631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4036204415053738426309589 94598540977821994366631)
                ·
                  rfl

theorem cell22_2487105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 7].length) (baseStart_2487105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487105 prefixEnd_2487105 := by exact prefixLift 2487105
  have htrace : WordTrace (prefixWord ++ tailWord_2487105) baseStart_2487105 baseEnd_2487105 := by
    simpa [prefixWord, tailWord_2487105, baseEnd_2487105] using wordTrace_append hprefix tailTrace_2487105
  have hstable : (prefixWord ++ tailWord_2487105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487105).length < 2 ^ (prefixWord ++ tailWord_2487105).sum := by decide
  have hdescent : baseEnd_2487105 < baseStart_2487105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487161 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 6]
def baseStart_2487161 : Nat := 118140960795 + 2487161 * 2 ^ 59
def prefixEnd_2487161 : Nat := 4983230072969 + 3 ^ 40 * 2487161 * 2
def baseEnd_2487161 : Nat := 283802012914944156633169

theorem tailTrace_2487161 : CollatzResearch.WordTrace tailWord_2487161 prefixEnd_2487161 283802012914944156633169 := by
  unfold tailWord_2487161
  simp only [CollatzResearch.WordTrace]
  refine ⟨90714214142447945125981337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60476142761631963417320891 90714214142447945125981337)
  ·
    refine ⟨68035660606835958844486003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90714214142447945125981337 68035660606835958844486003)
    ·
      refine ⟨102053490910253938266729005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68035660606835958844486003 102053490910253938266729005)
      ·
        refine ⟨38270059091345226850023377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102053490910253938266729005 38270059091345226850023377)
        ·
          refine ⟨28702544318508920137517533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38270059091345226850023377 28702544318508920137517533)
          ·
            refine ⟨10763454119440845051569075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28702544318508920137517533 10763454119440845051569075)
            ·
              refine ⟨16145181179161267577353613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10763454119440845051569075 16145181179161267577353613)
              ·
                refine ⟨6054442942185475341507605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16145181179161267577353613 6054442942185475341507605)
                ·
                  refine ⟨283802012914944156633169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6054442942185475341507605 283802012914944156633169)
                  ·
                    rfl

theorem cell22_2487161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_2487161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487161 prefixEnd_2487161 := by exact prefixLift 2487161
  have htrace : WordTrace (prefixWord ++ tailWord_2487161) baseStart_2487161 baseEnd_2487161 := by
    simpa [prefixWord, tailWord_2487161, baseEnd_2487161] using wordTrace_append hprefix tailTrace_2487161
  have hstable : (prefixWord ++ tailWord_2487161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487161).length < 2 ^ (prefixWord ++ tailWord_2487161).sum := by decide
  have hdescent : baseEnd_2487161 < baseStart_2487161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487178 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_2487178 : Nat := 118140960795 + 2487178 * 2 ^ 59
def prefixEnd_2487178 : Nat := 4983230072969 + 3 ^ 40 * 2487178 * 2
def baseEnd_2487178 : Nat := 283803952730750030741485

theorem tailTrace_2487178 : CollatzResearch.WordTrace tailWord_2487178 prefixEnd_2487178 283803952730750030741485 := by
  unfold tailWord_2487178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22678708545846589257337547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60476556122257571352900125 22678708545846589257337547)
  ·
    refine ⟨34018062818769883886006321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22678708545846589257337547 34018062818769883886006321)
    ·
      refine ⟨25513547114077412914504741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34018062818769883886006321 25513547114077412914504741)
      ·
        refine ⟨4783790083889514921469639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25513547114077412914504741 4783790083889514921469639)
        ·
          refine ⟨7175685125834272382204459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783790083889514921469639 7175685125834272382204459)
          ·
            refine ⟨10763527688751408573306689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175685125834272382204459 10763527688751408573306689)
            ·
              refine ⟨8072645766563556429980017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10763527688751408573306689 8072645766563556429980017)
              ·
                refine ⟨6054484324922667322485013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8072645766563556429980017 6054484324922667322485013)
                ·
                  refine ⟨283803952730750030741485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6054484324922667322485013 283803952730750030741485)
                  ·
                    rfl

theorem cell22_2487178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_2487178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487178 prefixEnd_2487178 := by exact prefixLift 2487178
  have htrace : WordTrace (prefixWord ++ tailWord_2487178) baseStart_2487178 baseEnd_2487178 := by
    simpa [prefixWord, tailWord_2487178, baseEnd_2487178] using wordTrace_append hprefix tailTrace_2487178
  have hstable : (prefixWord ++ tailWord_2487178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487178).length < 2 ^ (prefixWord ++ tailWord_2487178).sum := by decide
  have hdescent : baseEnd_2487178 < baseStart_2487178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487191 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2487191 : Nat := 118140960795 + 2487191 * 2 ^ 59
def prefixEnd_2487191 : Nat := 4983230072969 + 3 ^ 40 * 2487191 * 2
def baseEnd_2487191 : Nat := 851416308357922391649415

theorem tailTrace_2487191 : CollatzResearch.WordTrace tailWord_2487191 prefixEnd_2487191 851416308357922391649415 := by
  unfold tailWord_2487191
  simp only [CollatzResearch.WordTrace]
  refine ⟨90715308332339260249573427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60476872221559506833048951 90715308332339260249573427)
  ·
    refine ⟨136072962498508890374360141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90715308332339260249573427 136072962498508890374360141)
    ·
      refine ⟨51027360936940833890385053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136072962498508890374360141 51027360936940833890385053)
      ·
        refine ⟨19135260351352812708894395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51027360936940833890385053 19135260351352812708894395)
        ·
          refine ⟨28702890527029219063341593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19135260351352812708894395 28702890527029219063341593)
          ·
            refine ⟨21527167895271914297506195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28702890527029219063341593 21527167895271914297506195)
            ·
              refine ⟨32290751842907871446259293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21527167895271914297506195 32290751842907871446259293)
              ·
                refine ⟨12109031941090451792347235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32290751842907871446259293 12109031941090451792347235)
                ·
                  refine ⟨18163547911635677688520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12109031941090451792347235 18163547911635677688520853)
                  ·
                    refine ⟨851416308357922391649415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18163547911635677688520853 851416308357922391649415)
                    ·
                      rfl

theorem cell22_2487191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2487191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487191 prefixEnd_2487191 := by exact prefixLift 2487191
  have htrace : WordTrace (prefixWord ++ tailWord_2487191) baseStart_2487191 baseEnd_2487191 := by
    simpa [prefixWord, tailWord_2487191, baseEnd_2487191] using wordTrace_append hprefix tailTrace_2487191
  have hstable : (prefixWord ++ tailWord_2487191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487191).length < 2 ^ (prefixWord ++ tailWord_2487191).sum := by decide
  have hdescent : baseEnd_2487191 < baseStart_2487191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487330 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2487330 : Nat := 118140960795 + 2487330 * 2 ^ 59
def prefixEnd_2487330 : Nat := 4983230072969 + 3 ^ 40 * 2487330 * 2
def baseEnd_2487330 : Nat := 283821296966190787474663

theorem tailTrace_2487330 : CollatzResearch.WordTrace tailWord_2487330 prefixEnd_2487330 283821296966190787474663 := by
  unfold tailWord_2487330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680094519708921747220861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60480252052557124659255629 22680094519708921747220861)
  ·
    refine ⟨8505035444890845655207823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22680094519708921747220861 8505035444890845655207823)
    ·
      refine ⟨12757553167336268482811735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8505035444890845655207823 12757553167336268482811735)
      ·
        refine ⟨19136329751004402724217603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12757553167336268482811735 19136329751004402724217603)
        ·
          refine ⟨28704494626506604086326405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19136329751004402724217603 28704494626506604086326405)
          ·
            refine ⟨5382092742469988266186201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28704494626506604086326405 5382092742469988266186201)
            ·
              refine ⟨4036569556852491199639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382092742469988266186201 4036569556852491199639651)
              ·
                refine ⟨6054854335278736799459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036569556852491199639651 6054854335278736799459477)
                ·
                  refine ⟨283821296966190787474663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6054854335278736799459477 283821296966190787474663)
                  ·
                    rfl

theorem cell22_2487330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2487330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487330 prefixEnd_2487330 := by exact prefixLift 2487330
  have htrace : WordTrace (prefixWord ++ tailWord_2487330) baseStart_2487330 baseEnd_2487330 := by
    simpa [prefixWord, tailWord_2487330, baseEnd_2487330] using wordTrace_append hprefix tailTrace_2487330
  have hstable : (prefixWord ++ tailWord_2487330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487330).length < 2 ^ (prefixWord ++ tailWord_2487330).sum := by decide
  have hdescent : baseEnd_2487330 < baseStart_2487330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487484 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2487484 : Nat := 118140960795 + 2487484 * 2 ^ 59
def prefixEnd_2487484 : Nat := 4983230072969 + 3 ^ 40 * 2487484 * 2
def baseEnd_2487484 : Nat := 851516608245767294073517

theorem tailTrace_2487484 : CollatzResearch.WordTrace tailWord_2487484 prefixEnd_2487484 851516608245767294073517 := by
  unfold tailWord_2487484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45362997460138885644994753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60483996613518514193326337 45362997460138885644994753)
  ·
    refine ⟨34022248095104164233746065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45362997460138885644994753 34022248095104164233746065)
    ·
      refine ⟨25516686071328123175309549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34022248095104164233746065 25516686071328123175309549)
      ·
        refine ⟨9568757276748046190741081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25516686071328123175309549 9568757276748046190741081)
        ·
          refine ⟨7176567957561034643055811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9568757276748046190741081 7176567957561034643055811)
          ·
            refine ⟨10764851936341551964583717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176567957561034643055811 10764851936341551964583717)
            ·
              refine ⟨2018409738064040993359447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10764851936341551964583717 2018409738064040993359447)
              ·
                refine ⟨3027614607096061490039171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018409738064040993359447 3027614607096061490039171)
                ·
                  refine ⟨4541421910644092235058757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027614607096061490039171 4541421910644092235058757)
                  ·
                    refine ⟨851516608245767294073517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541421910644092235058757 851516608245767294073517)
                    ·
                      rfl

theorem cell22_2487484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2487484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487484 prefixEnd_2487484 := by exact prefixLift 2487484
  have htrace : WordTrace (prefixWord ++ tailWord_2487484) baseStart_2487484 baseEnd_2487484 := by
    simpa [prefixWord, tailWord_2487484, baseEnd_2487484] using wordTrace_append hprefix tailTrace_2487484
  have hstable : (prefixWord ++ tailWord_2487484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487484).length < 2 ^ (prefixWord ++ tailWord_2487484).sum := by decide
  have hdescent : baseEnd_2487484 < baseStart_2487484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487495 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2487495 : Nat := 118140960795 + 2487495 * 2 ^ 59
def prefixEnd_2487495 : Nat := 4983230072969 + 3 ^ 40 * 2487495 * 2
def baseEnd_2487495 : Nat := 851520373770566932048483

theorem tailTrace_2487495 : CollatzResearch.WordTrace tailWord_2487495 prefixEnd_2487495 851520373770566932048483 := by
  unfold tailWord_2487495
  simp only [CollatzResearch.WordTrace]
  refine ⟨90726396123237920168639939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60484264082158613445759959 90726396123237920168639939)
  ·
    refine ⟨136089594184856880252959909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90726396123237920168639939 136089594184856880252959909)
    ·
      refine ⟨25516798909660665047429983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136089594184856880252959909 25516798909660665047429983)
      ·
        refine ⟨38275198364490997571144975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25516798909660665047429983 38275198364490997571144975)
        ·
          refine ⟨57412797546736496356717463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38275198364490997571144975 57412797546736496356717463)
          ·
            refine ⟨86119196320104744535076195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57412797546736496356717463 86119196320104744535076195)
            ·
              refine ⟨129178794480157116802614293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86119196320104744535076195 129178794480157116802614293)
              ·
                refine ⟨6055255991257364850122545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129178794480157116802614293 6055255991257364850122545)
                ·
                  refine ⟨4541441993443023637591909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055255991257364850122545 4541441993443023637591909)
                  ·
                    refine ⟨851520373770566932048483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541441993443023637591909 851520373770566932048483)
                    ·
                      rfl

theorem cell22_2487495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2487495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487495 prefixEnd_2487495 := by exact prefixLift 2487495
  have htrace : WordTrace (prefixWord ++ tailWord_2487495) baseStart_2487495 baseEnd_2487495 := by
    simpa [prefixWord, tailWord_2487495, baseEnd_2487495] using wordTrace_append hprefix tailTrace_2487495
  have hstable : (prefixWord ++ tailWord_2487495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487495).length < 2 ^ (prefixWord ++ tailWord_2487495).sum := by decide
  have hdescent : baseEnd_2487495 < baseStart_2487495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487527 : List Nat := [1, 1, 5, 3, 2, 1, 1, 8]
def baseStart_2487527 : Nat := 118140960795 + 2487527 * 2 ^ 59
def prefixEnd_2487527 : Nat := 4983230072969 + 3 ^ 40 * 2487527 * 2
def baseEnd_2487527 : Nat := 94614592002725501694265

theorem tailTrace_2487527 : CollatzResearch.WordTrace tailWord_2487527 prefixEnd_2487527 94614592002725501694265 := by
  unfold tailWord_2487527
  simp only [CollatzResearch.WordTrace]
  refine ⟨90727563259121989633804835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60485042172747993089203223 90727563259121989633804835)
  ·
    refine ⟨136091344888682984450707253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90727563259121989633804835 136091344888682984450707253)
    ·
      refine ⟨12758563583314029792253805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136091344888682984450707253 12758563583314029792253805)
      ·
        refine ⟨4784461343742761172095177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12758563583314029792253805 4784461343742761172095177)
        ·
          refine ⟨3588346007807070879071383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784461343742761172095177 3588346007807070879071383)
          ·
            refine ⟨5382519011710606318607075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588346007807070879071383 5382519011710606318607075)
            ·
              refine ⟨8073778517565909477910613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382519011710606318607075 8073778517565909477910613)
              ·
                refine ⟨94614592002725501694265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8073778517565909477910613 94614592002725501694265)
                ·
                  rfl

theorem cell22_2487527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 8].length) (baseStart_2487527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487527 prefixEnd_2487527 := by exact prefixLift 2487527
  have htrace : WordTrace (prefixWord ++ tailWord_2487527) baseStart_2487527 baseEnd_2487527 := by
    simpa [prefixWord, tailWord_2487527, baseEnd_2487527] using wordTrace_append hprefix tailTrace_2487527
  have hstable : (prefixWord ++ tailWord_2487527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487527).length < 2 ^ (prefixWord ++ tailWord_2487527).sum := by decide
  have hdescent : baseEnd_2487527 < baseStart_2487527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487555 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 7]
def baseStart_2487555 : Nat := 118140960795 + 2487555 * 2 ^ 59
def prefixEnd_2487555 : Nat := 4983230072969 + 3 ^ 40 * 2487555 * 2
def baseEnd_2487555 : Nat := 283846970998915591849433

theorem tailTrace_2487555 : CollatzResearch.WordTrace tailWord_2487555 prefixEnd_2487555 283846970998915591849433 := by
  unfold tailWord_2487555
  simp only [CollatzResearch.WordTrace]
  refine ⟨90728584503020550415824119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60485723002013700277216079 90728584503020550415824119)
  ·
    refine ⟨136092876754530825623736179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90728584503020550415824119 136092876754530825623736179)
    ·
      refine ⟨204139315131796238435604269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136092876754530825623736179 204139315131796238435604269)
      ·
        refine ⟨76552243174423589413351601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204139315131796238435604269 76552243174423589413351601)
        ·
          refine ⟨57414182380817692060013701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76552243174423589413351601 57414182380817692060013701)
          ·
            refine ⟨10765159196403317261252569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57414182380817692060013701 10765159196403317261252569)
            ·
              refine ⟨8073869397302487945939427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10765159196403317261252569 8073869397302487945939427)
              ·
                refine ⟨12110804095953731918909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073869397302487945939427 12110804095953731918909141)
                ·
                  refine ⟨283846970998915591849433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12110804095953731918909141 283846970998915591849433)
                  ·
                    rfl

theorem cell22_2487555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_2487555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487555 prefixEnd_2487555 := by exact prefixLift 2487555
  have htrace : WordTrace (prefixWord ++ tailWord_2487555) baseStart_2487555 baseEnd_2487555 := by
    simpa [prefixWord, tailWord_2487555, baseEnd_2487555] using wordTrace_append hprefix tailTrace_2487555
  have hstable : (prefixWord ++ tailWord_2487555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487555).length < 2 ^ (prefixWord ++ tailWord_2487555).sum := by decide
  have hdescent : baseEnd_2487555 < baseStart_2487555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487632 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_2487632 : Nat := 118140960795 + 2487632 * 2 ^ 59
def prefixEnd_2487632 : Nat := 4983230072969 + 3 ^ 40 * 2487632 * 2
def baseEnd_2487632 : Nat := 851567271670344241373063

theorem tailTrace_2487632 : CollatzResearch.WordTrace tailWord_2487632 prefixEnd_2487632 851567271670344241373063 := by
  unfold tailWord_2487632
  simp only [CollatzResearch.WordTrace]
  refine ⟨45365696461870796283188575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60487595282494395044251433 45365696461870796283188575)
  ·
    refine ⟨68048544692806194424782863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45365696461870796283188575 68048544692806194424782863)
    ·
      refine ⟨102072817039209291637174295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68048544692806194424782863 102072817039209291637174295)
      ·
        refine ⟨153109225558813937455761443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102072817039209291637174295 153109225558813937455761443)
        ·
          refine ⟨229663838338220906183642165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153109225558813937455761443 229663838338220906183642165)
          ·
            refine ⟨21530984844208209954716453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229663838338220906183642165 21530984844208209954716453)
            ·
              refine ⟨4037059658289039366509335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21530984844208209954716453 4037059658289039366509335)
              ·
                refine ⟨6055589487433559049764003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037059658289039366509335 6055589487433559049764003)
                ·
                  refine ⟨9083384231150338574646005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055589487433559049764003 9083384231150338574646005)
                  ·
                    refine ⟨851567271670344241373063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9083384231150338574646005 851567271670344241373063)
                    ·
                      rfl

theorem cell22_2487632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_2487632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487632 prefixEnd_2487632 := by exact prefixLift 2487632
  have htrace : WordTrace (prefixWord ++ tailWord_2487632) baseStart_2487632 baseEnd_2487632 := by
    simpa [prefixWord, tailWord_2487632, baseEnd_2487632] using wordTrace_append hprefix tailTrace_2487632
  have hstable : (prefixWord ++ tailWord_2487632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487632).length < 2 ^ (prefixWord ++ tailWord_2487632).sum := by decide
  have hdescent : baseEnd_2487632 < baseStart_2487632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487752 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_2487752 : Nat := 118140960795 + 2487752 * 2 ^ 59
def prefixEnd_2487752 : Nat := 4983230072969 + 3 ^ 40 * 2487752 * 2
def baseEnd_2487752 : Nat := 283869450040901309457565

theorem tailTrace_2487752 : CollatzResearch.WordTrace tailWord_2487752 prefixEnd_2487752 283869450040901309457565 := by
  unfold tailWord_2487752
  simp only [CollatzResearch.WordTrace]
  refine ⟨45367884841653426530372755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60490513122204568707163673 45367884841653426530372755)
  ·
    refine ⟨68051827262480139795559133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45367884841653426530372755 68051827262480139795559133)
    ·
      refine ⟨25519435223430052423334675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68051827262480139795559133 25519435223430052423334675)
      ·
        refine ⟨38279152835145078635002013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25519435223430052423334675 38279152835145078635002013)
        ·
          refine ⟨14354682313179404488125755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38279152835145078635002013 14354682313179404488125755)
          ·
            refine ⟨21532023469769106732188633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14354682313179404488125755 21532023469769106732188633)
            ·
              refine ⟨16149017602326830049141475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21532023469769106732188633 16149017602326830049141475)
              ·
                refine ⟨24223526403490245073712213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16149017602326830049141475 24223526403490245073712213)
                ·
                  refine ⟨283869450040901309457565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24223526403490245073712213 283869450040901309457565)
                  ·
                    rfl

theorem cell22_2487752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_2487752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487752 prefixEnd_2487752 := by exact prefixLift 2487752
  have htrace : WordTrace (prefixWord ++ tailWord_2487752) baseStart_2487752 baseEnd_2487752 := by
    simpa [prefixWord, tailWord_2487752, baseEnd_2487752] using wordTrace_append hprefix tailTrace_2487752
  have hstable : (prefixWord ++ tailWord_2487752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487752).length < 2 ^ (prefixWord ++ tailWord_2487752).sum := by decide
  have hdescent : baseEnd_2487752 < baseStart_2487752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487754 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2487754 : Nat := 118140960795 + 2487754 * 2 ^ 59
def prefixEnd_2487754 : Nat := 4983230072969 + 3 ^ 40 * 2487754 * 2
def baseEnd_2487754 : Nat := 851609034763576589822689

theorem tailTrace_2487754 : CollatzResearch.WordTrace tailWord_2487754 prefixEnd_2487754 851609034763576589822689 := by
  unfold tailWord_2487754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22683960657324901850579579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60490561752866404934878877 22683960657324901850579579)
  ·
    refine ⟨34025940985987352775869369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22683960657324901850579579 34025940985987352775869369)
    ·
      refine ⟨25519455739490514581902027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34025940985987352775869369 25519455739490514581902027)
      ·
        refine ⟨38279183609235771872853041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25519455739490514581902027 38279183609235771872853041)
        ·
          refine ⟨28709387706926828904639781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38279183609235771872853041 28709387706926828904639781)
          ·
            refine ⟨5383010195048780419619959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28709387706926828904639781 5383010195048780419619959)
            ·
              refine ⟨8074515292573170629429939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5383010195048780419619959 8074515292573170629429939)
              ·
                refine ⟨12111772938859755944144909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074515292573170629429939 12111772938859755944144909)
                ·
                  refine ⟨4541914852072408479054341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12111772938859755944144909 4541914852072408479054341)
                  ·
                    refine ⟨851609034763576589822689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541914852072408479054341 851609034763576589822689)
                    ·
                      rfl

theorem cell22_2487754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2487754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487754 prefixEnd_2487754 := by exact prefixLift 2487754
  have htrace : WordTrace (prefixWord ++ tailWord_2487754) baseStart_2487754 baseEnd_2487754 := by
    simpa [prefixWord, tailWord_2487754, baseEnd_2487754] using wordTrace_append hprefix tailTrace_2487754
  have hstable : (prefixWord ++ tailWord_2487754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487754).length < 2 ^ (prefixWord ++ tailWord_2487754).sum := by decide
  have hdescent : baseEnd_2487754 < baseStart_2487754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487919 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_2487919 : Nat := 118140960795 + 2487919 * 2 ^ 59
def prefixEnd_2487919 : Nat := 4983230072969 + 3 ^ 40 * 2487919 * 2
def baseEnd_2487919 : Nat := 851665517635571159447183

theorem tailTrace_2487919 : CollatzResearch.WordTrace tailWord_2487919 prefixEnd_2487919 851665517635571159447183 := by
  unfold tailWord_2487919
  simp only [CollatzResearch.WordTrace]
  refine ⟨90741860673701840582074811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60494573782467893721383207 90741860673701840582074811)
  ·
    refine ⟨136112791010552760873112217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90741860673701840582074811 136112791010552760873112217)
    ·
      refine ⟨102084593257914570654834163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136112791010552760873112217 102084593257914570654834163)
      ·
        refine ⟨153126889886871855982251245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102084593257914570654834163 153126889886871855982251245)
        ·
          refine ⟨57422583707576945993344217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153126889886871855982251245 57422583707576945993344217)
          ·
            refine ⟨43066937780682709495008163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57422583707576945993344217 43066937780682709495008163)
            ·
              refine ⟨64600406671024064242512245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43066937780682709495008163 64600406671024064242512245)
              ·
                refine ⟨6056288125408506022735523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64600406671024064242512245 6056288125408506022735523)
                ·
                  refine ⟨9084432188112759034103285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056288125408506022735523 9084432188112759034103285)
                  ·
                    refine ⟨851665517635571159447183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9084432188112759034103285 851665517635571159447183)
                    ·
                      rfl

theorem cell22_2487919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_2487919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487919 prefixEnd_2487919 := by exact prefixLift 2487919
  have htrace : WordTrace (prefixWord ++ tailWord_2487919) baseStart_2487919 baseEnd_2487919 := by
    simpa [prefixWord, tailWord_2487919, baseEnd_2487919] using wordTrace_append hprefix tailTrace_2487919
  have hstable : (prefixWord ++ tailWord_2487919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487919).length < 2 ^ (prefixWord ++ tailWord_2487919).sum := by decide
  have hdescent : baseEnd_2487919 < baseStart_2487919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487940 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2487940 : Nat := 118140960795 + 2487940 * 2 ^ 59
def prefixEnd_2487940 : Nat := 4983230072969 + 3 ^ 40 * 2487940 * 2
def baseEnd_2487940 : Nat := 851672706364734104672119

theorem tailTrace_2487940 : CollatzResearch.WordTrace tailWord_2487940 prefixEnd_2487940 851672706364734104672119 := by
  unfold tailWord_2487940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45371313303312880584294637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60495084404417174112392849 45371313303312880584294637)
  ·
    refine ⟨17014242488742330219110489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45371313303312880584294637 17014242488742330219110489)
    ·
      refine ⟨12760681866556747664332867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17014242488742330219110489 12760681866556747664332867)
      ·
        refine ⟨19141022799835121496499301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12760681866556747664332867 19141022799835121496499301)
        ·
          refine ⟨3588941774969085280593619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19141022799835121496499301 3588941774969085280593619)
          ·
            refine ⟨5383412662453627920890429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588941774969085280593619 5383412662453627920890429)
            ·
              refine ⟨2018779748420110470333911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5383412662453627920890429 2018779748420110470333911)
              ·
                refine ⟨3028169622630165705500867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018779748420110470333911 3028169622630165705500867)
                ·
                  refine ⟨4542254433945248558251301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028169622630165705500867 4542254433945248558251301)
                  ·
                    refine ⟨851672706364734104672119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542254433945248558251301 851672706364734104672119)
                    ·
                      rfl

theorem cell22_2487940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2487940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487940 prefixEnd_2487940 := by exact prefixLift 2487940
  have htrace : WordTrace (prefixWord ++ tailWord_2487940) baseStart_2487940 baseEnd_2487940 := by
    simpa [prefixWord, tailWord_2487940, baseEnd_2487940] using wordTrace_append hprefix tailTrace_2487940
  have hstable : (prefixWord ++ tailWord_2487940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487940).length < 2 ^ (prefixWord ++ tailWord_2487940).sum := by decide
  have hdescent : baseEnd_2487940 < baseStart_2487940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487970 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2487970 : Nat := 118140960795 + 2487970 * 2 ^ 59
def prefixEnd_2487970 : Nat := 4983230072969 + 3 ^ 40 * 2487970 * 2
def baseEnd_2487970 : Nat := 851682975977824026422027

theorem tailTrace_2487970 : CollatzResearch.WordTrace tailWord_2487970 prefixEnd_2487970 851682975977824026422027 := by
  unfold tailWord_2487970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22685930199129269073045341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60495813864344717528120909 22685930199129269073045341)
  ·
    refine ⟨8507223824673475902392003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22685930199129269073045341 8507223824673475902392003)
    ·
      refine ⟨12760835737010213853588005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8507223824673475902392003 12760835737010213853588005)
      ·
        refine ⟨2392656700689415097547751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12760835737010213853588005 2392656700689415097547751)
        ·
          refine ⟨3588985051034122646321627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392656700689415097547751 3588985051034122646321627)
          ·
            refine ⟨5383477576551183969482441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588985051034122646321627 5383477576551183969482441)
            ·
              refine ⟨4037608182413387977111831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5383477576551183969482441 4037608182413387977111831)
              ·
                refine ⟨6056412273620081965667747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037608182413387977111831 6056412273620081965667747)
                ·
                  refine ⟨9084618410430122948501621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056412273620081965667747 9084618410430122948501621)
                  ·
                    refine ⟨851682975977824026422027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9084618410430122948501621 851682975977824026422027)
                    ·
                      rfl

theorem cell22_2487970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2487970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2487970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2487970 prefixEnd_2487970 := by exact prefixLift 2487970
  have htrace : WordTrace (prefixWord ++ tailWord_2487970) baseStart_2487970 baseEnd_2487970 := by
    simpa [prefixWord, tailWord_2487970, baseEnd_2487970] using wordTrace_append hprefix tailTrace_2487970
  have hstable : (prefixWord ++ tailWord_2487970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487970).length < 2 ^ (prefixWord ++ tailWord_2487970).sum := by decide
  have hdescent : baseEnd_2487970 < baseStart_2487970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488026 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_2488026 : Nat := 118140960795 + 2488026 * 2 ^ 59
def prefixEnd_2488026 : Nat := 4983230072969 + 3 ^ 40 * 2488026 * 2
def baseEnd_2488026 : Nat := 851702145922258547021855

theorem tailTrace_2488026 : CollatzResearch.WordTrace tailWord_2488026 prefixEnd_2488026 851702145922258547021855 := by
  unfold tailWord_2488026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22686440821078549464054983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60497175522876131904146621 22686440821078549464054983)
  ·
    refine ⟨34029661231617824196082475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22686440821078549464054983 34029661231617824196082475)
    ·
      refine ⟨51044491847426736294123713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34029661231617824196082475 51044491847426736294123713)
      ·
        refine ⟨38283368885570052220592785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51044491847426736294123713 38283368885570052220592785)
        ·
          refine ⟨28712526664177539165444589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38283368885570052220592785 28712526664177539165444589)
          ·
            refine ⟨10767197499066577187041721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28712526664177539165444589 10767197499066577187041721)
            ·
              refine ⟨8075398124299932890281291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10767197499066577187041721 8075398124299932890281291)
              ·
                refine ⟨12113097186449899335421937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8075398124299932890281291 12113097186449899335421937)
                ·
                  refine ⟨9084822889837424501566453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12113097186449899335421937 9084822889837424501566453)
                  ·
                    refine ⟨851702145922258547021855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9084822889837424501566453 851702145922258547021855)
                    ·
                      rfl

theorem cell22_2488026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_2488026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488026 prefixEnd_2488026 := by exact prefixLift 2488026
  have htrace : WordTrace (prefixWord ++ tailWord_2488026) baseStart_2488026 baseEnd_2488026 := by
    simpa [prefixWord, tailWord_2488026, baseEnd_2488026] using wordTrace_append hprefix tailTrace_2488026
  have hstable : (prefixWord ++ tailWord_2488026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488026).length < 2 ^ (prefixWord ++ tailWord_2488026).sum := by decide
  have hdescent : baseEnd_2488026 < baseStart_2488026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488101 : List Nat := [1, 3, 1, 2, 3, 2, 2, 8]
def baseStart_2488101 : Nat := 118140960795 + 2488101 * 2 ^ 59
def prefixEnd_2488101 : Nat := 4983230072969 + 3 ^ 40 * 2488101 * 2
def baseEnd_2488101 : Nat := 94636424439442594599625

theorem tailTrace_2488101 : CollatzResearch.WordTrace tailWord_2488101 prefixEnd_2488101 94636424439442594599625 := by
  unfold tailWord_2488101
  simp only [CollatzResearch.WordTrace]
  refine ⟨90748498759042485665200157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60498999172694990443466771 90748498759042485665200157)
  ·
    refine ⟨34030687034640932124450059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90748498759042485665200157 34030687034640932124450059)
    ·
      refine ⟨51046030551961398186675089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34030687034640932124450059 51046030551961398186675089)
      ·
        refine ⟨38284522913971048640006317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51046030551961398186675089 38284522913971048640006317)
        ·
          refine ⟨14356696092739143240002369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38284522913971048640006317 14356696092739143240002369)
          ·
            refine ⟨10767522069554357430001777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14356696092739143240002369 10767522069554357430001777)
            ·
              refine ⟨8075641552165768072501333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10767522069554357430001777 8075641552165768072501333)
              ·
                refine ⟨94636424439442594599625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8075641552165768072501333 94636424439442594599625)
                ·
                  rfl

theorem cell22_2488101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 8].length) (baseStart_2488101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488101 prefixEnd_2488101 := by exact prefixLift 2488101
  have htrace : WordTrace (prefixWord ++ tailWord_2488101) baseStart_2488101 baseEnd_2488101 := by
    simpa [prefixWord, tailWord_2488101, baseEnd_2488101] using wordTrace_append hprefix tailTrace_2488101
  have hstable : (prefixWord ++ tailWord_2488101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488101).length < 2 ^ (prefixWord ++ tailWord_2488101).sum := by decide
  have hdescent : baseEnd_2488101 < baseStart_2488101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488118 : List Nat := [5, 1, 2, 2, 1, 11]
def baseStart_2488118 : Nat := 118140960795 + 2488118 * 2 ^ 59
def prefixEnd_2488118 : Nat := 4983230072969 + 3 ^ 40 * 2488118 * 2
def baseEnd_2488118 : Nat := 10515230116079024366933

theorem tailTrace_2488118 : CollatzResearch.WordTrace tailWord_2488118 prefixEnd_2488118 10515230116079024366933 := by
  unfold tailWord_2488118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671819924998806098035563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60499412533320598379046005 5671819924998806098035563)
  ·
    refine ⟨8507729887498209147053345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671819924998806098035563 8507729887498209147053345)
    ·
      refine ⟨6380797415623656860290009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8507729887498209147053345 6380797415623656860290009)
      ·
        refine ⟨4785598061717742645217507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380797415623656860290009 4785598061717742645217507)
        ·
          refine ⟨7178397092576613967826261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785598061717742645217507 7178397092576613967826261)
          ·
            refine ⟨10515230116079024366933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7178397092576613967826261 10515230116079024366933)
            ·
              rfl

theorem cell22_2488118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 11].length) (baseStart_2488118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488118 prefixEnd_2488118 := by exact prefixLift 2488118
  have htrace : WordTrace (prefixWord ++ tailWord_2488118) baseStart_2488118 baseEnd_2488118 := by
    simpa [prefixWord, tailWord_2488118, baseEnd_2488118] using wordTrace_append hprefix tailTrace_2488118
  have hstable : (prefixWord ++ tailWord_2488118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488118).length < 2 ^ (prefixWord ++ tailWord_2488118).sum := by decide
  have hdescent : baseEnd_2488118 < baseStart_2488118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488131 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_2488131 : Nat := 118140960795 + 2488131 * 2 ^ 59
def prefixEnd_2488131 : Nat := 4983230072969 + 3 ^ 40 * 2488131 * 2
def baseEnd_2488131 : Nat := 851738089568073273146533

theorem tailTrace_2488131 : CollatzResearch.WordTrace tailWord_2488131 prefixEnd_2488131 851738089568073273146533 := by
  unfold tailWord_2488131
  simp only [CollatzResearch.WordTrace]
  refine ⟨90749592948933800788792247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60499728632622533859194831 90749592948933800788792247)
  ·
    refine ⟨136124389423400701183188371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90749592948933800788792247 136124389423400701183188371)
    ·
      refine ⟨204186584135101051774782557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136124389423400701183188371 204186584135101051774782557)
      ·
        refine ⟨76569969050662894415543459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204186584135101051774782557 76569969050662894415543459)
        ·
          refine ⟨114854953575994341623315189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76569969050662894415543459 114854953575994341623315189)
          ·
            refine ⟨10767651897749469527185799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114854953575994341623315189 10767651897749469527185799)
            ·
              refine ⟨16151477846624204290778699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10767651897749469527185799 16151477846624204290778699)
              ·
                refine ⟨24227216769936306436168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16151477846624204290778699 24227216769936306436168049)
                ·
                  refine ⟨18170412577452229827126037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24227216769936306436168049 18170412577452229827126037)
                  ·
                    refine ⟨851738089568073273146533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18170412577452229827126037 851738089568073273146533)
                    ·
                      rfl

theorem cell22_2488131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_2488131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488131 prefixEnd_2488131 := by exact prefixLift 2488131
  have htrace : WordTrace (prefixWord ++ tailWord_2488131) baseStart_2488131 baseEnd_2488131 := by
    simpa [prefixWord, tailWord_2488131, baseEnd_2488131] using wordTrace_append hprefix tailTrace_2488131
  have hstable : (prefixWord ++ tailWord_2488131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488131).length < 2 ^ (prefixWord ++ tailWord_2488131).sum := by decide
  have hdescent : baseEnd_2488131 < baseStart_2488131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488133 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_2488133 : Nat := 118140960795 + 2488133 * 2 ^ 59
def prefixEnd_2488133 : Nat := 4983230072969 + 3 ^ 40 * 2488133 * 2
def baseEnd_2488133 : Nat := 851738774208945934596527

theorem tailTrace_2488133 : CollatzResearch.WordTrace tailWord_2488133 prefixEnd_2488133 851738774208945934596527 := by
  unfold tailWord_2488133
  simp only [CollatzResearch.WordTrace]
  refine ⟨90749665894926555130365053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60499777263284370086910035 90749665894926555130365053)
  ·
    refine ⟨34031124710597458173886895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90749665894926555130365053 34031124710597458173886895)
    ·
      refine ⟨51046687065896187260830343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34031124710597458173886895 51046687065896187260830343)
      ·
        refine ⟨76570030598844280891245515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51046687065896187260830343 76570030598844280891245515)
        ·
          refine ⟨114855045898266421336868273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76570030598844280891245515 114855045898266421336868273)
          ·
            refine ⟨86141284423699816002651205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114855045898266421336868273 86141284423699816002651205)
            ·
              refine ⟨16151490829443715500497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86141284423699816002651205 16151490829443715500497101)
              ·
                refine ⟨6056809061041393312686413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16151490829443715500497101 6056809061041393312686413)
                ·
                  refine ⟨2271303397890522492257405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6056809061041393312686413 2271303397890522492257405)
                  ·
                    refine ⟨851738774208945934596527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271303397890522492257405 851738774208945934596527)
                    ·
                      rfl

theorem cell22_2488133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_2488133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488133 prefixEnd_2488133 := by exact prefixLift 2488133
  have htrace : WordTrace (prefixWord ++ tailWord_2488133) baseStart_2488133 baseEnd_2488133 := by
    simpa [prefixWord, tailWord_2488133, baseEnd_2488133] using wordTrace_append hprefix tailTrace_2488133
  have hstable : (prefixWord ++ tailWord_2488133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488133).length < 2 ^ (prefixWord ++ tailWord_2488133).sum := by decide
  have hdescent : baseEnd_2488133 < baseStart_2488133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488161 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2488161 : Nat := 118140960795 + 2488161 * 2 ^ 59
def prefixEnd_2488161 : Nat := 4983230072969 + 3 ^ 40 * 2488161 * 2
def baseEnd_2488161 : Nat := 851748359181163194896441

theorem tailTrace_2488161 : CollatzResearch.WordTrace tailWord_2488161 prefixEnd_2488161 851748359181163194896441 := by
  unfold tailWord_2488161
  simp only [CollatzResearch.WordTrace]
  refine ⟨90750687138825115912384337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60500458092550077274922891 90750687138825115912384337)
  ·
    refine ⟨68063015354118836934288253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90750687138825115912384337 68063015354118836934288253)
    ·
      refine ⟨25523630757794563850358095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68063015354118836934288253 25523630757794563850358095)
      ·
        refine ⟨38285446136691845775537143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25523630757794563850358095 38285446136691845775537143)
        ·
          refine ⟨57428169205037768663305715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38285446136691845775537143 57428169205037768663305715)
          ·
            refine ⟨86142253807556652994958573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57428169205037768663305715 86142253807556652994958573)
            ·
              refine ⟨32303345177833744873109465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86142253807556652994958573 32303345177833744873109465)
              ·
                refine ⟨24227508883375308654832099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32303345177833744873109465 24227508883375308654832099)
                ·
                  refine ⟨36341263325062962982248149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24227508883375308654832099 36341263325062962982248149)
                  ·
                    refine ⟨851748359181163194896441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36341263325062962982248149 851748359181163194896441)
                    ·
                      rfl

theorem cell22_2488161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2488161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488161 prefixEnd_2488161 := by exact prefixLift 2488161
  have htrace : WordTrace (prefixWord ++ tailWord_2488161) baseStart_2488161 baseEnd_2488161 := by
    simpa [prefixWord, tailWord_2488161, baseEnd_2488161] using wordTrace_append hprefix tailTrace_2488161
  have hstable : (prefixWord ++ tailWord_2488161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488161).length < 2 ^ (prefixWord ++ tailWord_2488161).sum := by decide
  have hdescent : baseEnd_2488161 < baseStart_2488161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488167 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2488167 : Nat := 118140960795 + 2488167 * 2 ^ 59
def prefixEnd_2488167 : Nat := 4983230072969 + 3 ^ 40 * 2488167 * 2
def baseEnd_2488167 : Nat := 851750413103781179246423

theorem tailTrace_2488167 : CollatzResearch.WordTrace tailWord_2488167 prefixEnd_2488167 851750413103781179246423 := by
  unfold tailWord_2488167
  simp only [CollatzResearch.WordTrace]
  refine ⟨90750905976803378937102755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60500603984535585958068503 90750905976803378937102755)
  ·
    refine ⟨136126358965205068405654133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90750905976803378937102755 136126358965205068405654133)
    ·
      refine ⟨12761846152987975163030075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136126358965205068405654133 12761846152987975163030075)
      ·
        refine ⟨19142769229481962744545113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12761846152987975163030075 19142769229481962744545113)
        ·
          refine ⟨14357076922111472058408835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19142769229481962744545113 14357076922111472058408835)
          ·
            refine ⟨21535615383167208087613253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14357076922111472058408835 21535615383167208087613253)
            ·
              refine ⟨4037927884343851516427485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21535615383167208087613253 4037927884343851516427485)
              ·
                refine ⟨1514222956628944318660307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4037927884343851516427485 1514222956628944318660307)
                ·
                  refine ⟨2271334434943416477990461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514222956628944318660307 2271334434943416477990461)
                  ·
                    refine ⟨851750413103781179246423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271334434943416477990461 851750413103781179246423)
                    ·
                      rfl

theorem cell22_2488167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2488167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488167 prefixEnd_2488167 := by exact prefixLift 2488167
  have htrace : WordTrace (prefixWord ++ tailWord_2488167) baseStart_2488167 baseEnd_2488167 := by
    simpa [prefixWord, tailWord_2488167, baseEnd_2488167] using wordTrace_append hprefix tailTrace_2488167
  have hstable : (prefixWord ++ tailWord_2488167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488167).length < 2 ^ (prefixWord ++ tailWord_2488167).sum := by decide
  have hdescent : baseEnd_2488167 < baseStart_2488167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488253 : List Nat := [1, 4, 1, 2, 3, 1, 1, 9]
def baseStart_2488253 : Nat := 118140960795 + 2488253 * 2 ^ 59
def prefixEnd_2488253 : Nat := 4983230072969 + 3 ^ 40 * 2488253 * 2
def baseEnd_2488253 : Nat := 94642205851256180177351

theorem tailTrace_2488253 : CollatzResearch.WordTrace tailWord_2488253 prefixEnd_2488253 94642205851256180177351 := by
  unfold tailWord_2488253
  simp only [CollatzResearch.WordTrace]
  refine ⟨90754042654491815624733413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60502695102994543749822275 90754042654491815624733413)
  ·
    refine ⟨17016382997717215429637515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90754042654491815624733413 17016382997717215429637515)
    ·
      refine ⟨25524574496575823144456273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016382997717215429637515 25524574496575823144456273)
      ·
        refine ⟨19143430872431867358342205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25524574496575823144456273 19143430872431867358342205)
        ·
          refine ⟨7178786577161950259378327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19143430872431867358342205 7178786577161950259378327)
          ·
            refine ⟨10768179865742925389067491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178786577161950259378327 10768179865742925389067491)
            ·
              refine ⟨16152269798614388083601237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10768179865742925389067491 16152269798614388083601237)
              ·
                refine ⟨94642205851256180177351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16152269798614388083601237 94642205851256180177351)
                ·
                  rfl

theorem cell22_2488253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 9].length) (baseStart_2488253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488253 prefixEnd_2488253 := by exact prefixLift 2488253
  have htrace : WordTrace (prefixWord ++ tailWord_2488253) baseStart_2488253 baseEnd_2488253 := by
    simpa [prefixWord, tailWord_2488253, baseEnd_2488253] using wordTrace_append hprefix tailTrace_2488253
  have hstable : (prefixWord ++ tailWord_2488253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488253).length < 2 ^ (prefixWord ++ tailWord_2488253).sum := by decide
  have hdescent : baseEnd_2488253 < baseStart_2488253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488313 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2488313 : Nat := 118140960795 + 2488313 * 2 ^ 59
def prefixEnd_2488313 : Nat := 4983230072969 + 3 ^ 40 * 2488313 * 2
def baseEnd_2488313 : Nat := 851800391887485465095975

theorem tailTrace_2488313 : CollatzResearch.WordTrace tailWord_2488313 prefixEnd_2488313 851800391887485465095975 := by
  unfold tailWord_2488313
  simp only [CollatzResearch.WordTrace]
  refine ⟨90756231034274445871917593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60504154022849630581278395 90756231034274445871917593)
  ·
    refine ⟨68067173275705834403938195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90756231034274445871917593 68067173275705834403938195)
    ·
      refine ⟨102100759913558751605907293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68067173275705834403938195 102100759913558751605907293)
      ·
        refine ⟨38287784967584531852215235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102100759913558751605907293 38287784967584531852215235)
        ·
          refine ⟨57431677451376797778322853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38287784967584531852215235 57431677451376797778322853)
          ·
            refine ⟨10768439522133149583435535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57431677451376797778322853 10768439522133149583435535)
            ·
              refine ⟨16152659283199724375153303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10768439522133149583435535 16152659283199724375153303)
              ·
                refine ⟨24228988924799586562729955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16152659283199724375153303 24228988924799586562729955)
                ·
                  refine ⟨36343483387199379844094933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24228988924799586562729955 36343483387199379844094933)
                  ·
                    refine ⟨851800391887485465095975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36343483387199379844094933 851800391887485465095975)
                    ·
                      rfl

theorem cell22_2488313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2488313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488313 prefixEnd_2488313 := by exact prefixLift 2488313
  have htrace : WordTrace (prefixWord ++ tailWord_2488313) baseStart_2488313 baseEnd_2488313 := by
    simpa [prefixWord, tailWord_2488313, baseEnd_2488313] using wordTrace_append hprefix tailTrace_2488313
  have hstable : (prefixWord ++ tailWord_2488313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488313).length < 2 ^ (prefixWord ++ tailWord_2488313).sum := by decide
  have hdescent : baseEnd_2488313 < baseStart_2488313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488375 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2488375 : Nat := 118140960795 + 2488375 * 2 ^ 59
def prefixEnd_2488375 : Nat := 4983230072969 + 3 ^ 40 * 2488375 * 2
def baseEnd_2488375 : Nat := 851821615754537970045785

theorem tailTrace_2488375 : CollatzResearch.WordTrace tailWord_2488375 prefixEnd_2488375 851821615754537970045785 := by
  unfold tailWord_2488375
  simp only [CollatzResearch.WordTrace]
  refine ⟨90758492360049830460674579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60505661573366553640449719 90758492360049830460674579)
  ·
    refine ⟨136137738540074745691011869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90758492360049830460674579 136137738540074745691011869)
    ·
      refine ⟨51051651952528029634129451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136137738540074745691011869 51051651952528029634129451)
      ·
        refine ⟨76577477928792044451194177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51051651952528029634129451 76577477928792044451194177)
        ·
          refine ⟨57433108446594033338395633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76577477928792044451194177 57433108446594033338395633)
          ·
            refine ⟨43074831334945525003796725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57433108446594033338395633 43074831334945525003796725)
            ·
              refine ⟨4038265437651142969105943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43074831334945525003796725 4038265437651142969105943)
              ·
                refine ⟨6057398156476714453658915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038265437651142969105943 6057398156476714453658915)
                ·
                  refine ⟨9086097234715071680488373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6057398156476714453658915 9086097234715071680488373)
                  ·
                    refine ⟨851821615754537970045785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9086097234715071680488373 851821615754537970045785)
                    ·
                      rfl

theorem cell22_2488375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2488375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488375 prefixEnd_2488375 := by exact prefixLift 2488375
  have htrace : WordTrace (prefixWord ++ tailWord_2488375) baseStart_2488375 baseEnd_2488375 := by
    simpa [prefixWord, tailWord_2488375, baseEnd_2488375] using wordTrace_append hprefix tailTrace_2488375
  have hstable : (prefixWord ++ tailWord_2488375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488375).length < 2 ^ (prefixWord ++ tailWord_2488375).sum := by decide
  have hdescent : baseEnd_2488375 < baseStart_2488375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_2488403 : Nat := 118140960795 + 2488403 * 2 ^ 59
def prefixEnd_2488403 : Nat := 4983230072969 + 3 ^ 40 * 2488403 * 2
def baseEnd_2488403 : Nat := 851831200726755230345699

theorem tailTrace_2488403 : CollatzResearch.WordTrace tailWord_2488403 prefixEnd_2488403 851831200726755230345699 := by
  unfold tailWord_2488403
  simp only [CollatzResearch.WordTrace]
  refine ⟨90759513603948391242693863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60506342402632260828462575 90759513603948391242693863)
  ·
    refine ⟨136139270405922586864040795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90759513603948391242693863 136139270405922586864040795)
    ·
      refine ⟨204208905608883880296061193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136139270405922586864040795 204208905608883880296061193)
      ·
        refine ⟨153156679206662910222045895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204208905608883880296061193 153156679206662910222045895)
        ·
          refine ⟨229735018809994365333068843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153156679206662910222045895 229735018809994365333068843)
          ·
            refine ⟨344602528214991547999603265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229735018809994365333068843 344602528214991547999603265)
            ·
              refine ⟨258451896161243660999702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344602528214991547999603265 258451896161243660999702449)
              ·
                refine ⟨193838922120932745749776837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258451896161243660999702449 193838922120932745749776837)
                ·
                  refine ⟨36344797897674889828083157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193838922120932745749776837 36344797897674889828083157)
                  ·
                    refine ⟨851831200726755230345699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36344797897674889828083157 851831200726755230345699)
                    ·
                      rfl

theorem cell22_2488403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_2488403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488403 prefixEnd_2488403 := by exact prefixLift 2488403
  have htrace : WordTrace (prefixWord ++ tailWord_2488403) baseStart_2488403 baseEnd_2488403 := by
    simpa [prefixWord, tailWord_2488403, baseEnd_2488403] using wordTrace_append hprefix tailTrace_2488403
  have hstable : (prefixWord ++ tailWord_2488403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488403).length < 2 ^ (prefixWord ++ tailWord_2488403).sum := by decide
  have hdescent : baseEnd_2488403 < baseStart_2488403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488405 : List Nat := [1, 3, 2, 2, 1, 5, 8]
def baseStart_2488405 : Nat := 118140960795 + 2488405 * 2 ^ 59
def prefixEnd_2488405 : Nat := 4983230072969 + 3 ^ 40 * 2488405 * 2
def baseEnd_2488405 : Nat := 31549329087689921918359

theorem tailTrace_2488405 : CollatzResearch.WordTrace tailWord_2488405 prefixEnd_2488405 31549329087689921918359 := by
  unfold tailWord_2488405
  simp only [CollatzResearch.WordTrace]
  refine ⟨90759586549941145584266669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60506391033294097056177779 90759586549941145584266669)
  ·
    refine ⟨34034844956227929594100001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90759586549941145584266669 34034844956227929594100001)
    ·
      refine ⟨25526133717170947195575001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34034844956227929594100001 25526133717170947195575001)
      ·
        refine ⟨19144600287878210396681251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25526133717170947195575001 19144600287878210396681251)
        ·
          refine ⟨28716900431817315595021877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19144600287878210396681251 28716900431817315595021877)
          ·
            refine ⟨2692209415482873337033301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28716900431817315595021877 2692209415482873337033301)
            ·
              refine ⟨31549329087689921918359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2692209415482873337033301 31549329087689921918359)
              ·
                rfl

theorem cell22_2488405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 8].length) (baseStart_2488405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488405 prefixEnd_2488405 := by exact prefixLift 2488405
  have htrace : WordTrace (prefixWord ++ tailWord_2488405) baseStart_2488405 baseEnd_2488405 := by
    simpa [prefixWord, tailWord_2488405, baseEnd_2488405] using wordTrace_append hprefix tailTrace_2488405
  have hstable : (prefixWord ++ tailWord_2488405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488405).length < 2 ^ (prefixWord ++ tailWord_2488405).sum := by decide
  have hdescent : baseEnd_2488405 < baseStart_2488405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488471 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2488471 : Nat := 118140960795 + 2488471 * 2 ^ 59
def prefixEnd_2488471 : Nat := 4983230072969 + 3 ^ 40 * 2488471 * 2
def baseEnd_2488471 : Nat := 851854478516425719645491

theorem tailTrace_2488471 : CollatzResearch.WordTrace tailWord_2488471 prefixEnd_2488471 851854478516425719645491 := by
  unfold tailWord_2488471
  simp only [CollatzResearch.WordTrace]
  refine ⟨90761993767702038856169267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60507995845134692570779511 90761993767702038856169267)
  ·
    refine ⟨136142990651553058284253901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90761993767702038856169267 136142990651553058284253901)
    ·
      refine ⟨51053621494332396856595213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136142990651553058284253901 51053621494332396856595213)
      ·
        refine ⟨19145108060374648821223205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51053621494332396856595213 19145108060374648821223205)
        ·
          refine ⟨3589707761320246653979351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19145108060374648821223205 3589707761320246653979351)
          ·
            refine ⟨5384561641980369980969027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589707761320246653979351 5384561641980369980969027)
            ·
              refine ⟨8076842462970554971453541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384561641980369980969027 8076842462970554971453541)
              ·
                refine ⟨1514407961806979057147539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8076842462970554971453541 1514407961806979057147539)
                ·
                  refine ⟨2271611942710468585721309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514407961806979057147539 2271611942710468585721309)
                  ·
                    refine ⟨851854478516425719645491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271611942710468585721309 851854478516425719645491)
                    ·
                      rfl

theorem cell22_2488471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2488471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488471 prefixEnd_2488471 := by exact prefixLift 2488471
  have htrace : WordTrace (prefixWord ++ tailWord_2488471) baseStart_2488471 baseEnd_2488471 := by
    simpa [prefixWord, tailWord_2488471, baseEnd_2488471] using wordTrace_append hprefix tailTrace_2488471
  have hstable : (prefixWord ++ tailWord_2488471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488471).length < 2 ^ (prefixWord ++ tailWord_2488471).sum := by decide
  have hdescent : baseEnd_2488471 < baseStart_2488471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488482 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2488482 : Nat := 118140960795 + 2488482 * 2 ^ 59
def prefixEnd_2488482 : Nat := 4983230072969 + 3 ^ 40 * 2488482 * 2
def baseEnd_2488482 : Nat := 851858244041225357620457

theorem tailTrace_2488482 : CollatzResearch.WordTrace tailWord_2488482 prefixEnd_2488482 851858244041225357620457 := by
  unfold tailWord_2488482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22690598742665546933704925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60508263313774791823213133 22690598742665546933704925)
  ·
    refine ⟨8508974528499580100139347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22690598742665546933704925 8508974528499580100139347)
    ·
      refine ⟨12763461792749370150209021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508974528499580100139347 12763461792749370150209021)
      ·
        refine ⟨4786298172281013806328383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12763461792749370150209021 4786298172281013806328383)
        ·
          refine ⟨7179447258421520709492575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786298172281013806328383 7179447258421520709492575)
          ·
            refine ⟨10769170887632281064238863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7179447258421520709492575 10769170887632281064238863)
            ·
              refine ⟨16153756331448421596358295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10769170887632281064238863 16153756331448421596358295)
              ·
                refine ⟨24230634497172632394537443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16153756331448421596358295 24230634497172632394537443)
                ·
                  refine ⟨36345951745758948591806165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24230634497172632394537443 36345951745758948591806165)
                  ·
                    refine ⟨851858244041225357620457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36345951745758948591806165 851858244041225357620457)
                    ·
                      rfl

theorem cell22_2488482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2488482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488482 prefixEnd_2488482 := by exact prefixLift 2488482
  have htrace : WordTrace (prefixWord ++ tailWord_2488482) baseStart_2488482 baseEnd_2488482 := by
    simpa [prefixWord, tailWord_2488482, baseEnd_2488482] using wordTrace_append hprefix tailTrace_2488482
  have hstable : (prefixWord ++ tailWord_2488482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488482).length < 2 ^ (prefixWord ++ tailWord_2488482).sum := by decide
  have hdescent : baseEnd_2488482 < baseStart_2488482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488527 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 4, 3]
def baseStart_2488527 : Nat := 118140960795 + 2488527 * 2 ^ 59
def prefixEnd_2488527 : Nat := 4983230072969 + 3 ^ 40 * 2488527 * 2
def baseEnd_2488527 : Nat := 851873648460860240245319

theorem tailTrace_2488527 : CollatzResearch.WordTrace tailWord_2488527 prefixEnd_2488527 851873648460860240245319 := by
  unfold tailWord_2488527
  simp only [CollatzResearch.WordTrace]
  refine ⟨90764036255499160420207835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60509357503666106946805223 90764036255499160420207835)
  ·
    refine ⟨136146054383248740630311753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90764036255499160420207835 136146054383248740630311753)
    ·
      refine ⟨102109540787436555472733815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136146054383248740630311753 102109540787436555472733815)
      ·
        refine ⟨153164311181154833209100723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102109540787436555472733815 153164311181154833209100723)
        ·
          refine ⟨229746466771732249813651085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153164311181154833209100723 229746466771732249813651085)
          ·
            refine ⟨86154925039399593680119157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229746466771732249813651085 86154925039399593680119157)
            ·
              refine ⟨8077024222443711907511171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86154925039399593680119157 8077024222443711907511171)
              ·
                refine ⟨12115536333665567861266757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077024222443711907511171 12115536333665567861266757)
                ·
                  refine ⟨2271663062562293973987517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12115536333665567861266757 2271663062562293973987517)
                  ·
                    refine ⟨851873648460860240245319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271663062562293973987517 851873648460860240245319)
                    ·
                      rfl

theorem cell22_2488527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_2488527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488527 prefixEnd_2488527 := by exact prefixLift 2488527
  have htrace : WordTrace (prefixWord ++ tailWord_2488527) baseStart_2488527 baseEnd_2488527 := by
    simpa [prefixWord, tailWord_2488527, baseEnd_2488527] using wordTrace_append hprefix tailTrace_2488527
  have hstable : (prefixWord ++ tailWord_2488527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488527).length < 2 ^ (prefixWord ++ tailWord_2488527).sum := by decide
  have hdescent : baseEnd_2488527 < baseStart_2488527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488555 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_2488555 : Nat := 118140960795 + 2488555 * 2 ^ 59
def prefixEnd_2488555 : Nat := 4983230072969 + 3 ^ 40 * 2488555 * 2
def baseEnd_2488555 : Nat := 851883233433077500545233

theorem tailTrace_2488555 : CollatzResearch.WordTrace tailWord_2488555 prefixEnd_2488555 851883233433077500545233 := by
  unfold tailWord_2488555
  simp only [CollatzResearch.WordTrace]
  refine ⟨90765057499397721202227119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60510038332931814134818079 90765057499397721202227119)
  ·
    refine ⟨136147586249096581803340679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90765057499397721202227119 136147586249096581803340679)
    ·
      refine ⟨204221379373644872705011019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136147586249096581803340679 204221379373644872705011019)
      ·
        refine ⟨306332069060467309057516529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204221379373644872705011019 306332069060467309057516529)
        ·
          refine ⟨229749051795350481793137397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306332069060467309057516529 229749051795350481793137397)
          ·
            refine ⟨21538973605814107668106631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229749051795350481793137397 21538973605814107668106631)
            ·
              refine ⟨32308460408721161502159947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21538973605814107668106631 32308460408721161502159947)
              ·
                refine ⟨48462690613081742253239921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32308460408721161502159947 48462690613081742253239921)
                ·
                  refine ⟨36347017959811306689929941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48462690613081742253239921 36347017959811306689929941)
                  ·
                    refine ⟨851883233433077500545233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36347017959811306689929941 851883233433077500545233)
                    ·
                      rfl

theorem cell22_2488555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_2488555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488555 prefixEnd_2488555 := by exact prefixLift 2488555
  have htrace : WordTrace (prefixWord ++ tailWord_2488555) baseStart_2488555 baseEnd_2488555 := by
    simpa [prefixWord, tailWord_2488555, baseEnd_2488555] using wordTrace_append hprefix tailTrace_2488555
  have hstable : (prefixWord ++ tailWord_2488555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488555).length < 2 ^ (prefixWord ++ tailWord_2488555).sum := by decide
  have hdescent : baseEnd_2488555 < baseStart_2488555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488647 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 6]
def baseStart_2488647 : Nat := 118140960795 + 2488647 * 2 ^ 59
def prefixEnd_2488647 : Nat := 4983230072969 + 3 ^ 40 * 2488647 * 2
def baseEnd_2488647 : Nat := 283971575637739975748317

theorem tailTrace_2488647 : CollatzResearch.WordTrace tailWord_2488647 prefixEnd_2488647 283971575637739975748317 := by
  unfold tailWord_2488647
  simp only [CollatzResearch.WordTrace]
  refine ⟨90768413015064420914576195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60512275343376280609717463 90768413015064420914576195)
  ·
    refine ⟨136152619522596631371864293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90768413015064420914576195 136152619522596631371864293)
    ·
      refine ⟨25528616160486868382224555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136152619522596631371864293 25528616160486868382224555)
      ·
        refine ⟨38292924240730302573336833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25528616160486868382224555 38292924240730302573336833)
        ·
          refine ⟨28719693180547726930002625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38292924240730302573336833 28719693180547726930002625)
          ·
            refine ⟨21539769885410795197501969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28719693180547726930002625 21539769885410795197501969)
            ·
              refine ⟨16154827414058096398126477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21539769885410795197501969 16154827414058096398126477)
              ·
                refine ⟨6058060280271786149297429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16154827414058096398126477 6058060280271786149297429)
                ·
                  refine ⟨283971575637739975748317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6058060280271786149297429 283971575637739975748317)
                  ·
                    rfl

theorem cell22_2488647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_2488647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488647 prefixEnd_2488647 := by exact prefixLift 2488647
  have htrace : WordTrace (prefixWord ++ tailWord_2488647) baseStart_2488647 baseEnd_2488647 := by
    simpa [prefixWord, tailWord_2488647, baseEnd_2488647] using wordTrace_append hprefix tailTrace_2488647
  have hstable : (prefixWord ++ tailWord_2488647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488647).length < 2 ^ (prefixWord ++ tailWord_2488647).sum := by decide
  have hdescent : baseEnd_2488647 < baseStart_2488647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488679 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2488679 : Nat := 118140960795 + 2488679 * 2 ^ 59
def prefixEnd_2488679 : Nat := 4983230072969 + 3 ^ 40 * 2488679 * 2
def baseEnd_2488679 : Nat := 851925681167182510444853

theorem tailTrace_2488679 : CollatzResearch.WordTrace tailWord_2488679 prefixEnd_2488679 851925681167182510444853 := by
  unfold tailWord_2488679
  simp only [CollatzResearch.WordTrace]
  refine ⟨90769580150948490379741091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60513053433965660253160727 90769580150948490379741091)
  ·
    refine ⟨136154370226422735569611637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90769580150948490379741091 136154370226422735569611637)
    ·
      refine ⟨12764472208727131459651091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136154370226422735569611637 12764472208727131459651091)
      ·
        refine ⟨19146708313090697189476637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764472208727131459651091 19146708313090697189476637)
        ·
          refine ⟨7180015617409011446053739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19146708313090697189476637 7180015617409011446053739)
          ·
            refine ⟨10770023426113517169080609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180015617409011446053739 10770023426113517169080609)
            ·
              refine ⟨8077517569585137876810457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10770023426113517169080609 8077517569585137876810457)
              ·
                refine ⟨6058138177188853407607843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8077517569585137876810457 6058138177188853407607843)
                ·
                  refine ⟨9087207265783280111411765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058138177188853407607843 9087207265783280111411765)
                  ·
                    refine ⟨851925681167182510444853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9087207265783280111411765 851925681167182510444853)
                    ·
                      rfl

theorem cell22_2488679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2488679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488679 prefixEnd_2488679 := by exact prefixLift 2488679
  have htrace : WordTrace (prefixWord ++ tailWord_2488679) baseStart_2488679 baseEnd_2488679 := by
    simpa [prefixWord, tailWord_2488679, baseEnd_2488679] using wordTrace_append hprefix tailTrace_2488679
  have hstable : (prefixWord ++ tailWord_2488679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488679).length < 2 ^ (prefixWord ++ tailWord_2488679).sum := by decide
  have hdescent : baseEnd_2488679 < baseStart_2488679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488713 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_2488713 : Nat := 118140960795 + 2488713 * 2 ^ 59
def prefixEnd_2488713 : Nat := 4983230072969 + 3 ^ 40 * 2488713 * 2
def baseEnd_2488713 : Nat := 851937320062017755094749

theorem tailTrace_2488713 : CollatzResearch.WordTrace tailWord_2488713 prefixEnd_2488713 851937320062017755094749 := by
  unfold tailWord_2488713
  simp only [CollatzResearch.WordTrace]
  refine ⟨90770820232825314186478793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60513880155216876124319195 90770820232825314186478793)
  ·
    refine ⟨68078115174618985639859095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90770820232825314186478793 68078115174618985639859095)
    ·
      refine ⟨102117172761928478459788643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68078115174618985639859095 102117172761928478459788643)
      ·
        refine ⟨153175759142892717689682965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102117172761928478459788643 153175759142892717689682965)
        ·
          refine ⟨7180113709823096141703889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153175759142892717689682965 7180113709823096141703889)
          ·
            refine ⟨5385085282367322106277917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180113709823096141703889 5385085282367322106277917)
            ·
              refine ⟨2019406980887745789854219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5385085282367322106277917 2019406980887745789854219)
              ·
                refine ⟨3029110471331618684781329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019406980887745789854219 3029110471331618684781329)
                ·
                  refine ⟨2271832853498714013585997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029110471331618684781329 2271832853498714013585997)
                  ·
                    refine ⟨851937320062017755094749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271832853498714013585997 851937320062017755094749)
                    ·
                      rfl

theorem cell22_2488713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_2488713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488713 prefixEnd_2488713 := by exact prefixLift 2488713
  have htrace : WordTrace (prefixWord ++ tailWord_2488713) baseStart_2488713 baseEnd_2488713 := by
    simpa [prefixWord, tailWord_2488713, baseEnd_2488713] using wordTrace_append hprefix tailTrace_2488713
  have hstable : (prefixWord ++ tailWord_2488713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488713).length < 2 ^ (prefixWord ++ tailWord_2488713).sum := by decide
  have hdescent : baseEnd_2488713 < baseStart_2488713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488754 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_2488754 : Nat := 118140960795 + 2488754 * 2 ^ 59
def prefixEnd_2488754 : Nat := 4983230072969 + 3 ^ 40 * 2488754 * 2
def baseEnd_2488754 : Nat := 283983785066635771606541

theorem tailTrace_2488754 : CollatzResearch.WordTrace tailWord_2488754 prefixEnd_2488754 283983785066635771606541 := by
  unfold tailWord_2488754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693078906419194547180329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60514877083784518792480877 22693078906419194547180329)
  ·
    refine ⟨17019809179814395910385247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22693078906419194547180329 17019809179814395910385247)
    ·
      refine ⟨25529713769721593865577871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17019809179814395910385247 25529713769721593865577871)
      ·
        refine ⟨38294570654582390798366807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25529713769721593865577871 38294570654582390798366807)
        ·
          refine ⟨57441855981873586197550211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38294570654582390798366807 57441855981873586197550211)
          ·
            refine ⟨86162783972810379296325317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57441855981873586197550211 86162783972810379296325317)
            ·
              refine ⟨16155521994901946118060997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86162783972810379296325317 16155521994901946118060997)
              ·
                refine ⟨3029160374044114897136437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16155521994901946118060997 3029160374044114897136437)
                ·
                  refine ⟨283983785066635771606541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029160374044114897136437 283983785066635771606541)
                  ·
                    rfl

theorem cell22_2488754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_2488754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488754 prefixEnd_2488754 := by exact prefixLift 2488754
  have htrace : WordTrace (prefixWord ++ tailWord_2488754) baseStart_2488754 baseEnd_2488754 := by
    simpa [prefixWord, tailWord_2488754, baseEnd_2488754] using wordTrace_append hprefix tailTrace_2488754
  have hstable : (prefixWord ++ tailWord_2488754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488754).length < 2 ^ (prefixWord ++ tailWord_2488754).sum := by decide
  have hdescent : baseEnd_2488754 < baseStart_2488754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488767 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_2488767 : Nat := 118140960795 + 2488767 * 2 ^ 59
def prefixEnd_2488767 : Nat := 4983230072969 + 3 ^ 40 * 2488767 * 2
def baseEnd_2488767 : Nat := 851955805365579614244583

theorem tailTrace_2488767 : CollatzResearch.WordTrace tailWord_2488767 prefixEnd_2488767 851955805365579614244583 := by
  unfold tailWord_2488767
  simp only [CollatzResearch.WordTrace]
  refine ⟨90772789774629681408944555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60515193183086454272629703 90772789774629681408944555)
  ·
    refine ⟨136159184661944522113416833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90772789774629681408944555 136159184661944522113416833)
    ·
      refine ⟨102119388496458391585062625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136159184661944522113416833 102119388496458391585062625)
      ·
        refine ⟨76589541372343793688796969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102119388496458391585062625 76589541372343793688796969)
        ·
          refine ⟨57442156029257845266597727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76589541372343793688796969 57442156029257845266597727)
          ·
            refine ⟨86163234043886767899896591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57442156029257845266597727 86163234043886767899896591)
            ·
              refine ⟨129244851065830151849844887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86163234043886767899896591 129244851065830151849844887)
              ·
                refine ⟨193867276598745227774767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129244851065830151849844887 193867276598745227774767331)
                ·
                  refine ⟨290800914898117841662150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193867276598745227774767331 290800914898117841662150997)
                  ·
                    refine ⟨851955805365579614244583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 290800914898117841662150997 851955805365579614244583)
                    ·
                      rfl

theorem cell22_2488767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_2488767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488767 prefixEnd_2488767 := by exact prefixLift 2488767
  have htrace : WordTrace (prefixWord ++ tailWord_2488767) baseStart_2488767 baseEnd_2488767 := by
    simpa [prefixWord, tailWord_2488767, baseEnd_2488767] using wordTrace_append hprefix tailTrace_2488767
  have hstable : (prefixWord ++ tailWord_2488767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488767).length < 2 ^ (prefixWord ++ tailWord_2488767).sum := by decide
  have hdescent : baseEnd_2488767 < baseStart_2488767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488816 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_2488816 : Nat := 118140960795 + 2488816 * 2 ^ 59
def prefixEnd_2488816 : Nat := 4983230072969 + 3 ^ 40 * 2488816 * 2
def baseEnd_2488816 : Nat := 283990859688986606589811

theorem tailTrace_2488816 : CollatzResearch.WordTrace tailWord_2488816 prefixEnd_2488816 283990859688986606589811 := by
  unfold tailWord_2488816
  simp only [CollatzResearch.WordTrace]
  refine ⟨45387288475726081388739151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60516384634301441851652201 45387288475726081388739151)
  ·
    refine ⟨68080932713589122083108727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45387288475726081388739151 68080932713589122083108727)
    ·
      refine ⟨102121399070383683124663091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68080932713589122083108727 102121399070383683124663091)
      ·
        refine ⟨153182098605575524686994637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102121399070383683124663091 153182098605575524686994637)
        ·
          refine ⟨57443286977090821757622989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153182098605575524686994637 57443286977090821757622989)
          ·
            refine ⟨21541232616409058159108621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57443286977090821757622989 21541232616409058159108621)
            ·
              refine ⟨8077962231153396809665733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21541232616409058159108621 8077962231153396809665733)
              ·
                refine ⟨1514617918341261901812325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8077962231153396809665733 1514617918341261901812325)
                ·
                  refine ⟨283990859688986606589811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1514617918341261901812325 283990859688986606589811)
                  ·
                    rfl

theorem cell22_2488816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_2488816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488816 prefixEnd_2488816 := by exact prefixLift 2488816
  have htrace : WordTrace (prefixWord ++ tailWord_2488816) baseStart_2488816 baseEnd_2488816 := by
    simpa [prefixWord, tailWord_2488816, baseEnd_2488816] using wordTrace_append hprefix tailTrace_2488816
  have hstable : (prefixWord ++ tailWord_2488816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488816).length < 2 ^ (prefixWord ++ tailWord_2488816).sum := by decide
  have hdescent : baseEnd_2488816 < baseStart_2488816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488829 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2488829 : Nat := 118140960795 + 2488829 * 2 ^ 59
def prefixEnd_2488829 : Nat := 4983230072969 + 3 ^ 40 * 2488829 * 2
def baseEnd_2488829 : Nat := 851977029232632119194393

theorem tailTrace_2488829 : CollatzResearch.WordTrace tailWord_2488829 prefixEnd_2488829 851977029232632119194393 := by
  unfold tailWord_2488829
  simp only [CollatzResearch.WordTrace]
  refine ⟨90775051100405065997701541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60516700733603377331801027 90775051100405065997701541)
  ·
    refine ⟨17020322081325949874569039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90775051100405065997701541 17020322081325949874569039)
    ·
      refine ⟨25530483121988924811853559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020322081325949874569039 25530483121988924811853559)
      ·
        refine ⟨38295724682983387217780339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25530483121988924811853559 38295724682983387217780339)
        ·
          refine ⟨57443587024475080826670509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38295724682983387217780339 57443587024475080826670509)
          ·
            refine ⟨21541345134178155310001441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57443587024475080826670509 21541345134178155310001441)
            ·
              refine ⟨16156008850633616482501081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21541345134178155310001441 16156008850633616482501081)
              ·
                refine ⟨12117006637975212361875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16156008850633616482501081 12117006637975212361875811)
                ·
                  refine ⟨18175509956962818542813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12117006637975212361875811 18175509956962818542813717)
                  ·
                    refine ⟨851977029232632119194393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18175509956962818542813717 851977029232632119194393)
                    ·
                      rfl

theorem cell22_2488829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2488829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488829 prefixEnd_2488829 := by exact prefixLift 2488829
  have htrace : WordTrace (prefixWord ++ tailWord_2488829) baseStart_2488829 baseEnd_2488829 := by
    simpa [prefixWord, tailWord_2488829, baseEnd_2488829] using wordTrace_append hprefix tailTrace_2488829
  have hstable : (prefixWord ++ tailWord_2488829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488829).length < 2 ^ (prefixWord ++ tailWord_2488829).sum := by decide
  have hdescent : baseEnd_2488829 < baseStart_2488829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488831 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 2, 3]
def baseStart_2488831 : Nat := 118140960795 + 2488831 * 2 ^ 59
def prefixEnd_2488831 : Nat := 4983230072969 + 3 ^ 40 * 2488831 * 2
def baseEnd_2488831 : Nat := 851977713873504780644387

theorem tailTrace_2488831 : CollatzResearch.WordTrace tailWord_2488831 prefixEnd_2488831 851977713873504780644387 := by
  unfold tailWord_2488831
  simp only [CollatzResearch.WordTrace]
  refine ⟨90775124046397820339274347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60516749364265213559516231 90775124046397820339274347)
  ·
    refine ⟨136162686069596730508911521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90775124046397820339274347 136162686069596730508911521)
    ·
      refine ⟨102122014552197547881683641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136162686069596730508911521 102122014552197547881683641)
      ·
        refine ⟨76591510914148160911262731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102122014552197547881683641 76591510914148160911262731)
        ·
          refine ⟨114887266371222241366894097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76591510914148160911262731 114887266371222241366894097)
          ·
            refine ⟨86165449778416681025170573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114887266371222241366894097 86165449778416681025170573)
            ·
              refine ⟨32312043666906255384438965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86165449778416681025170573 32312043666906255384438965)
              ·
                refine ⟨3029254093772461442291153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32312043666906255384438965 3029254093772461442291153)
                ·
                  refine ⟨2271940570329346081718365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029254093772461442291153 2271940570329346081718365)
                  ·
                    refine ⟨851977713873504780644387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271940570329346081718365 851977713873504780644387)
                    ·
                      rfl

theorem cell22_2488831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_2488831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488831 prefixEnd_2488831 := by exact prefixLift 2488831
  have htrace : WordTrace (prefixWord ++ tailWord_2488831) baseStart_2488831 baseEnd_2488831 := by
    simpa [prefixWord, tailWord_2488831, baseEnd_2488831] using wordTrace_append hprefix tailTrace_2488831
  have hstable : (prefixWord ++ tailWord_2488831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488831).length < 2 ^ (prefixWord ++ tailWord_2488831).sum := by decide
  have hdescent : baseEnd_2488831 < baseStart_2488831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488846 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2488846 : Nat := 118140960795 + 2488846 * 2 ^ 59
def prefixEnd_2488846 : Nat := 4983230072969 + 3 ^ 40 * 2488846 * 2
def baseEnd_2488846 : Nat := 851982848680049741519341

theorem tailTrace_2488846 : CollatzResearch.WordTrace tailWord_2488846 prefixEnd_2488846 851982848680049741519341 := by
  unfold tailWord_2488846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11346958892667934737633799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60517114094228985267380261 11346958892667934737633799)
  ·
    refine ⟨17020438339001902106450699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11346958892667934737633799 17020438339001902106450699)
    ·
      refine ⟨25530657508502853159676049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020438339001902106450699 25530657508502853159676049)
      ·
        refine ⟨19147993131377139869757037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25530657508502853159676049 19147993131377139869757037)
        ·
          refine ⟨7180497424266427451158889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19147993131377139869757037 7180497424266427451158889)
          ·
            refine ⟨5385373068199820588369167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180497424266427451158889 5385373068199820588369167)
            ·
              refine ⟨8078059602299730882553751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385373068199820588369167 8078059602299730882553751)
              ·
                refine ⟨12117089403449596323830627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078059602299730882553751 12117089403449596323830627)
                ·
                  refine ⟨18175634105174394485745941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12117089403449596323830627 18175634105174394485745941)
                  ·
                    refine ⟨851982848680049741519341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18175634105174394485745941 851982848680049741519341)
                    ·
                      rfl

theorem cell22_2488846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2488846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488846 prefixEnd_2488846 := by exact prefixLift 2488846
  have htrace : WordTrace (prefixWord ++ tailWord_2488846) baseStart_2488846 baseEnd_2488846 := by
    simpa [prefixWord, tailWord_2488846, baseEnd_2488846] using wordTrace_append hprefix tailTrace_2488846
  have hstable : (prefixWord ++ tailWord_2488846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488846).length < 2 ^ (prefixWord ++ tailWord_2488846).sum := by decide
  have hdescent : baseEnd_2488846 < baseStart_2488846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488852 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2488852 : Nat := 118140960795 + 2488852 * 2 ^ 59
def prefixEnd_2488852 : Nat := 4983230072969 + 3 ^ 40 * 2488852 * 2
def baseEnd_2488852 : Nat := 851984902602667725869323

theorem tailTrace_2488852 : CollatzResearch.WordTrace tailWord_2488852 prefixEnd_2488852 851984902602667725869323 := by
  unfold tailWord_2488852
  simp only [CollatzResearch.WordTrace]
  refine ⟨45387944989660870462894405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60517259986214493950525873 45387944989660870462894405)
  ·
    refine ⟨8510239685561413211792701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45387944989660870462894405 8510239685561413211792701)
    ·
      refine ⟨3191339882085529954422263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8510239685561413211792701 3191339882085529954422263)
      ·
        refine ⟨4787009823128294931633395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191339882085529954422263 4787009823128294931633395)
        ·
          refine ⟨7180514734692442397450093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787009823128294931633395 7180514734692442397450093)
          ·
            refine ⟨2692693025509665899043785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7180514734692442397450093 2692693025509665899043785)
            ·
              refine ⟨2019519769132249424282839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2692693025509665899043785 2019519769132249424282839)
              ·
                refine ⟨3029279653698374136424259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019519769132249424282839 3029279653698374136424259)
                ·
                  refine ⟨4543919480547561204636389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029279653698374136424259 4543919480547561204636389)
                  ·
                    refine ⟨851984902602667725869323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4543919480547561204636389 851984902602667725869323)
                    ·
                      rfl

theorem cell22_2488852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2488852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488852 prefixEnd_2488852 := by exact prefixLift 2488852
  have htrace : WordTrace (prefixWord ++ tailWord_2488852) baseStart_2488852 baseEnd_2488852 := by
    simpa [prefixWord, tailWord_2488852, baseEnd_2488852] using wordTrace_append hprefix tailTrace_2488852
  have hstable : (prefixWord ++ tailWord_2488852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488852).length < 2 ^ (prefixWord ++ tailWord_2488852).sum := by decide
  have hdescent : baseEnd_2488852 < baseStart_2488852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488893 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2488893 : Nat := 118140960795 + 2488893 * 2 ^ 59
def prefixEnd_2488893 : Nat := 4983230072969 + 3 ^ 40 * 2488893 * 2
def baseEnd_2488893 : Nat := 851998937740557285594197

theorem tailTrace_2488893 : CollatzResearch.WordTrace tailWord_2488893 prefixEnd_2488893 851998937740557285594197 := by
  unfold tailWord_2488893
  simp only [CollatzResearch.WordTrace]
  refine ⟨90777385372173204928031333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60518256914782136618687555 90777385372173204928031333)
  ·
    refine ⟨17020759757282475924005875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90777385372173204928031333 17020759757282475924005875)
    ·
      refine ⟨25531139635923713886008813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020759757282475924005875 25531139635923713886008813)
      ·
        refine ⟨9574177363471392707253305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25531139635923713886008813 9574177363471392707253305)
        ·
          refine ⟨7180633022603544530439979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9574177363471392707253305 7180633022603544530439979)
          ·
            refine ⟨10770949533905316795659969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180633022603544530439979 10770949533905316795659969)
            ·
              refine ⟨8078212150428987596744977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10770949533905316795659969 8078212150428987596744977)
              ·
                refine ⟨6058659112821740697558733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8078212150428987596744977 6058659112821740697558733)
                ·
                  refine ⟨2271997167308152761584525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6058659112821740697558733 2271997167308152761584525)
                  ·
                    refine ⟨851998937740557285594197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271997167308152761584525 851998937740557285594197)
                    ·
                      rfl

theorem cell22_2488893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2488893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488893 prefixEnd_2488893 := by exact prefixLift 2488893
  have htrace : WordTrace (prefixWord ++ tailWord_2488893) baseStart_2488893 baseEnd_2488893 := by
    simpa [prefixWord, tailWord_2488893, baseEnd_2488893] using wordTrace_append hprefix tailTrace_2488893
  have hstable : (prefixWord ++ tailWord_2488893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488893).length < 2 ^ (prefixWord ++ tailWord_2488893).sum := by decide
  have hdescent : baseEnd_2488893 < baseStart_2488893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488904 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2488904 : Nat := 118140960795 + 2488904 * 2 ^ 59
def prefixEnd_2488904 : Nat := 4983230072969 + 3 ^ 40 * 2488904 * 2
def baseEnd_2488904 : Nat := 852002703265356923569163

theorem tailTrace_2488904 : CollatzResearch.WordTrace tailWord_2488904 prefixEnd_2488904 852002703265356923569163 := by
  unfold tailWord_2488904
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388893287566676903340883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60518524383422235871121177 45388893287566676903340883)
  ·
    refine ⟨68083339931350015355011325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45388893287566676903340883 68083339931350015355011325)
    ·
      refine ⟨25531252474256255758129247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68083339931350015355011325 25531252474256255758129247)
      ·
        refine ⟨38296878711384383637193871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25531252474256255758129247 38296878711384383637193871)
        ·
          refine ⟨57445318067076575455790807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38296878711384383637193871 57445318067076575455790807)
          ·
            refine ⟨86167977100614863183686211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57445318067076575455790807 86167977100614863183686211)
            ·
              refine ⟨129251965650922294775529317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86167977100614863183686211 129251965650922294775529317)
              ·
                refine ⟨24234743559547930270411747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129251965650922294775529317 24234743559547930270411747)
                ·
                  refine ⟨36352115339321895405617621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24234743559547930270411747 36352115339321895405617621)
                  ·
                    refine ⟨852002703265356923569163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36352115339321895405617621 852002703265356923569163)
                    ·
                      rfl

theorem cell22_2488904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2488904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488904 prefixEnd_2488904 := by exact prefixLift 2488904
  have htrace : WordTrace (prefixWord ++ tailWord_2488904) baseStart_2488904 baseEnd_2488904 := by
    simpa [prefixWord, tailWord_2488904, baseEnd_2488904] using wordTrace_append hprefix tailTrace_2488904
  have hstable : (prefixWord ++ tailWord_2488904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488904).length < 2 ^ (prefixWord ++ tailWord_2488904).sum := by decide
  have hdescent : baseEnd_2488904 < baseStart_2488904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488910 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_2488910 : Nat := 118140960795 + 2488910 * 2 ^ 59
def prefixEnd_2488910 : Nat := 4983230072969 + 3 ^ 40 * 2488910 * 2
def baseEnd_2488910 : Nat := 852004757187974907919145

theorem tailTrace_2488910 : CollatzResearch.WordTrace tailWord_2488910 prefixEnd_2488910 852004757187974907919145 := by
  unfold tailWord_2488910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347250676638952103925023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60518670275407744554266789 11347250676638952103925023)
  ·
    refine ⟨17020876014958428155887535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11347250676638952103925023 17020876014958428155887535)
    ·
      refine ⟨25531314022437642233831303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020876014958428155887535 25531314022437642233831303)
      ·
        refine ⟨38296971033656463350746955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25531314022437642233831303 38296971033656463350746955)
        ·
          refine ⟨57445456550484695026120433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38296971033656463350746955 57445456550484695026120433)
          ·
            refine ⟨43084092412863521269590325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57445456550484695026120433 43084092412863521269590325)
            ·
              refine ⟨4039133663705955119024093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43084092412863521269590325 4039133663705955119024093)
              ·
                refine ⟨1514675123889733169634035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4039133663705955119024093 1514675123889733169634035)
                ·
                  refine ⟨2272012685834599754451053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514675123889733169634035 2272012685834599754451053)
                  ·
                    refine ⟨852004757187974907919145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272012685834599754451053 852004757187974907919145)
                    ·
                      rfl

theorem cell22_2488910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_2488910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488910 prefixEnd_2488910 := by exact prefixLift 2488910
  have htrace : WordTrace (prefixWord ++ tailWord_2488910) baseStart_2488910 baseEnd_2488910 := by
    simpa [prefixWord, tailWord_2488910, baseEnd_2488910] using wordTrace_append hprefix tailTrace_2488910
  have hstable : (prefixWord ++ tailWord_2488910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488910).length < 2 ^ (prefixWord ++ tailWord_2488910).sum := by decide
  have hdescent : baseEnd_2488910 < baseStart_2488910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488953 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2488953 : Nat := 118140960795 + 2488953 * 2 ^ 59
def prefixEnd_2488953 : Nat := 4983230072969 + 3 ^ 40 * 2488953 * 2
def baseEnd_2488953 : Nat := 852019476966737129094013

theorem tailTrace_2488953 : CollatzResearch.WordTrace tailWord_2488953 prefixEnd_2488953 852019476966737129094013 := by
  unfold tailWord_2488953
  simp only [CollatzResearch.WordTrace]
  refine ⟨90779573751955835175215513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60519715834637223450143675 90779573751955835175215513)
  ·
    refine ⟨68084680313966876381411635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90779573751955835175215513 68084680313966876381411635)
    ·
      refine ⟨102127020470950314572117453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68084680313966876381411635 102127020470950314572117453)
      ·
        refine ⟨38297632676606367964544045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102127020470950314572117453 38297632676606367964544045)
        ·
          refine ⟨14361612253727387986704017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38297632676606367964544045 14361612253727387986704017)
          ·
            refine ⟨10771209190295540990028013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14361612253727387986704017 10771209190295540990028013)
            ·
              refine ⟨4039203446360827871260505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10771209190295540990028013 4039203446360827871260505)
              ·
                refine ⟨3029402584770620903445379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039203446360827871260505 3029402584770620903445379)
                ·
                  refine ⟨4544103877155931355168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029402584770620903445379 4544103877155931355168069)
                  ·
                    refine ⟨852019476966737129094013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4544103877155931355168069 852019476966737129094013)
                    ·
                      rfl

theorem cell22_2488953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2488953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2488953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2488953 prefixEnd_2488953 := by exact prefixLift 2488953
  have htrace : WordTrace (prefixWord ++ tailWord_2488953) baseStart_2488953 baseEnd_2488953 := by
    simpa [prefixWord, tailWord_2488953, baseEnd_2488953] using wordTrace_append hprefix tailTrace_2488953
  have hstable : (prefixWord ++ tailWord_2488953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488953).length < 2 ^ (prefixWord ++ tailWord_2488953).sum := by decide
  have hdescent : baseEnd_2488953 < baseStart_2488953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489015 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 2, 4]
def baseStart_2489015 : Nat := 118140960795 + 2489015 * 2 ^ 59
def prefixEnd_2489015 : Nat := 4983230072969 + 3 ^ 40 * 2489015 * 2
def baseEnd_2489015 : Nat := 852040700833789634043823

theorem tailTrace_2489015 : CollatzResearch.WordTrace tailWord_2489015 prefixEnd_2489015 852040700833789634043823 := by
  unfold tailWord_2489015
  simp only [CollatzResearch.WordTrace]
  refine ⟨90781835077731219763972499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60521223385154146509314999 90781835077731219763972499)
  ·
    refine ⟨136172752616596829645958749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90781835077731219763972499 136172752616596829645958749)
    ·
      refine ⟨51064782231223811117234531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136172752616596829645958749 51064782231223811117234531)
      ·
        refine ⟨76597173346835716675851797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51064782231223811117234531 76597173346835716675851797)
        ·
          refine ⟨3590492500632924219180553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76597173346835716675851797 3590492500632924219180553)
          ·
            refine ⟨2692869375474693164385415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590492500632924219180553 2692869375474693164385415)
            ·
              refine ⟨4039304063212039746578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692869375474693164385415 4039304063212039746578123)
              ·
                refine ⟨6058956094818059619867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039304063212039746578123 6058956094818059619867185)
                ·
                  refine ⟨4544217071113544714900389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6058956094818059619867185 4544217071113544714900389)
                  ·
                    refine ⟨852040700833789634043823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4544217071113544714900389 852040700833789634043823)
                    ·
                      rfl

theorem cell22_2489015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_2489015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489015 prefixEnd_2489015 := by exact prefixLift 2489015
  have htrace : WordTrace (prefixWord ++ tailWord_2489015) baseStart_2489015 baseEnd_2489015 := by
    simpa [prefixWord, tailWord_2489015, baseEnd_2489015] using wordTrace_append hprefix tailTrace_2489015
  have hstable : (prefixWord ++ tailWord_2489015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489015).length < 2 ^ (prefixWord ++ tailWord_2489015).sum := by decide
  have hdescent : baseEnd_2489015 < baseStart_2489015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489041 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 7]
def baseStart_2489041 : Nat := 118140960795 + 2489041 * 2 ^ 59
def prefixEnd_2489041 : Nat := 4983230072969 + 3 ^ 40 * 2489041 * 2
def baseEnd_2489041 : Nat := 284016533721711410964581

theorem tailTrace_2489041 : CollatzResearch.WordTrace tailWord_2489041 prefixEnd_2489041 284016533721711410964581 := by
  unfold tailWord_2489041
  simp only [CollatzResearch.WordTrace]
  refine ⟨90782783375637026204418977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60521855583758017469612651 90782783375637026204418977)
  ·
    refine ⟨68087087531727769653314233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90782783375637026204418977 68087087531727769653314233)
    ·
      refine ⟨51065315648795827239985675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68087087531727769653314233 51065315648795827239985675)
      ·
        refine ⟨76597973473193740859978513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51065315648795827239985675 76597973473193740859978513)
        ·
          refine ⟨57448480104895305644983885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76597973473193740859978513 57448480104895305644983885)
          ·
            refine ⟨21543180039335739616868957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57448480104895305644983885 21543180039335739616868957)
            ·
              refine ⟨8078692514750902356325859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21543180039335739616868957 8078692514750902356325859)
              ·
                refine ⟨12118038772126353534488789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078692514750902356325859 12118038772126353534488789)
                ·
                  refine ⟨284016533721711410964581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12118038772126353534488789 284016533721711410964581)
                  ·
                    rfl

theorem cell22_2489041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_2489041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489041 prefixEnd_2489041 := by exact prefixLift 2489041
  have htrace : WordTrace (prefixWord ++ tailWord_2489041) baseStart_2489041 baseEnd_2489041 := by
    simpa [prefixWord, tailWord_2489041, baseEnd_2489041] using wordTrace_append hprefix tailTrace_2489041
  have hstable : (prefixWord ++ tailWord_2489041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489041).length < 2 ^ (prefixWord ++ tailWord_2489041).sum := by decide
  have hdescent : baseEnd_2489041 < baseStart_2489041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489122 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2489122 : Nat := 118140960795 + 2489122 * 2 ^ 59
def prefixEnd_2489122 : Nat := 4983230072969 + 3 ^ 40 * 2489122 * 2
def baseEnd_2489122 : Nat := 852077329120477021618495

theorem tailTrace_2489122 : CollatzResearch.WordTrace tailWord_2489122 prefixEnd_2489122 852077329120477021618495 := by
  unfold tailWord_2489122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22696434422085894259529405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60523825125562384692078413 22696434422085894259529405)
  ·
    refine ⟨8511162908282210347323527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22696434422085894259529405 8511162908282210347323527)
    ·
      refine ⟨12766744362423315520985291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511162908282210347323527 12766744362423315520985291)
      ·
        refine ⟨19150116543634973281477937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12766744362423315520985291 19150116543634973281477937)
        ·
          refine ⟨14362587407726229961108453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19150116543634973281477937 14362587407726229961108453)
          ·
            refine ⟨2692985138948668117707835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14362587407726229961108453 2692985138948668117707835)
            ·
              refine ⟨4039477708423002176561753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692985138948668117707835 4039477708423002176561753)
              ·
                refine ⟨3029608281317251632421315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039477708423002176561753 3029608281317251632421315)
                ·
                  refine ⟨4544412421975877448631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029608281317251632421315 4544412421975877448631973)
                  ·
                    refine ⟨852077329120477021618495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4544412421975877448631973 852077329120477021618495)
                    ·
                      rfl

theorem cell22_2489122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2489122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489122 prefixEnd_2489122 := by exact prefixLift 2489122
  have htrace : WordTrace (prefixWord ++ tailWord_2489122) baseStart_2489122 baseEnd_2489122 := by
    simpa [prefixWord, tailWord_2489122, baseEnd_2489122] using wordTrace_append hprefix tailTrace_2489122
  have hstable : (prefixWord ++ tailWord_2489122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489122).length < 2 ^ (prefixWord ++ tailWord_2489122).sum := by decide
  have hdescent : baseEnd_2489122 < baseStart_2489122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489163 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 9, 3]
def baseStart_2489163 : Nat := 118140960795 + 2489163 * 2 ^ 59
def prefixEnd_2489163 : Nat := 4983230072969 + 3 ^ 40 * 2489163 * 2
def baseEnd_2489163 : Nat := 852091364258366581343369

theorem tailTrace_2489163 : CollatzResearch.WordTrace tailWord_2489163 prefixEnd_2489163 852091364258366581343369 := by
  unfold tailWord_2489163
  simp only [CollatzResearch.WordTrace]
  refine ⟨90787233081195041040360143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60524822054130027360240095 90787233081195041040360143)
  ·
    refine ⟨136180849621792561560540215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90787233081195041040360143 136180849621792561560540215)
    ·
      refine ⟨204271274432688842340810323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136180849621792561560540215 204271274432688842340810323)
      ·
        refine ⟨306406911649033263511215485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204271274432688842340810323 306406911649033263511215485)
        ·
          refine ⟨114902591868387473816705807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306406911649033263511215485 114902591868387473816705807)
          ·
            refine ⟨172353887802581210725058711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114902591868387473816705807 172353887802581210725058711)
            ·
              refine ⟨258530831703871816087588067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172353887802581210725058711 258530831703871816087588067)
              ·
                refine ⟨387796247555807724131382101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258530831703871816087588067 387796247555807724131382101)
                ·
                  refine ⟨2272243638022310883582317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 387796247555807724131382101 2272243638022310883582317)
                  ·
                    refine ⟨852091364258366581343369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272243638022310883582317 852091364258366581343369)
                    ·
                      rfl

theorem cell22_2489163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].length) (baseStart_2489163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489163 prefixEnd_2489163 := by exact prefixLift 2489163
  have htrace : WordTrace (prefixWord ++ tailWord_2489163) baseStart_2489163 baseEnd_2489163 := by
    simpa [prefixWord, tailWord_2489163, baseEnd_2489163] using wordTrace_append hprefix tailTrace_2489163
  have hstable : (prefixWord ++ tailWord_2489163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489163).length < 2 ^ (prefixWord ++ tailWord_2489163).sum := by decide
  have hdescent : baseEnd_2489163 < baseStart_2489163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489300 : List Nat := [2, 4, 1, 2, 1, 2, 2, 8]
def baseStart_2489300 : Nat := 118140960795 + 2489300 * 2 ^ 59
def prefixEnd_2489300 : Nat := 4983230072969 + 3 ^ 40 * 2489300 * 2
def baseEnd_2489300 : Nat := 94682029128682654518661

theorem tailTrace_2489300 : CollatzResearch.WordTrace tailWord_2489300 prefixEnd_2489300 94682029128682654518661 := by
  unfold tailWord_2489300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45396114940849356719048677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60528153254465808958731569 45396114940849356719048677)
  ·
    refine ⟨8511771551409254384821627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45396114940849356719048677 8511771551409254384821627)
    ·
      refine ⟨12767657327113881577232441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511771551409254384821627 12767657327113881577232441)
      ·
        refine ⟨9575742995335411182924331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12767657327113881577232441 9575742995335411182924331)
        ·
          refine ⟨14363614493003116774386497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9575742995335411182924331 14363614493003116774386497)
          ·
            refine ⟨10772710869752337580789873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14363614493003116774386497 10772710869752337580789873)
            ·
              refine ⟨8079533152314253185592405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10772710869752337580789873 8079533152314253185592405)
              ·
                refine ⟨94682029128682654518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8079533152314253185592405 94682029128682654518661)
                ·
                  rfl

theorem cell22_2489300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_2489300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489300 prefixEnd_2489300 := by exact prefixLift 2489300
  have htrace : WordTrace (prefixWord ++ tailWord_2489300) baseStart_2489300 baseEnd_2489300 := by
    simpa [prefixWord, tailWord_2489300, baseEnd_2489300] using wordTrace_append hprefix tailTrace_2489300
  have hstable : (prefixWord ++ tailWord_2489300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489300).length < 2 ^ (prefixWord ++ tailWord_2489300).sum := by decide
  have hdescent : baseEnd_2489300 < baseStart_2489300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489317 : List Nat := [1, 3, 1, 6, 2, 9]
def baseStart_2489317 : Nat := 118140960795 + 2489317 * 2 ^ 59
def prefixEnd_2489317 : Nat := 4983230072969 + 3 ^ 40 * 2489317 * 2
def baseEnd_2489317 : Nat := 10520297303772364357937

theorem tailTrace_2489317 : CollatzResearch.WordTrace tailWord_2489317 prefixEnd_2489317 10520297303772364357937 := by
  unfold tailWord_2489317
  simp only [CollatzResearch.WordTrace]
  refine ⟨90792849922637125341466205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60528566615091416894310803 90792849922637125341466205)
  ·
    refine ⟨34047318720988922003049827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90792849922637125341466205 34047318720988922003049827)
    ·
      refine ⟨51070978081483383004574741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34047318720988922003049827 51070978081483383004574741)
      ·
        refine ⟨2393952097569533578339441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51070978081483383004574741 2393952097569533578339441)
        ·
          refine ⟨1795464073177150183754581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2393952097569533578339441 1795464073177150183754581)
          ·
            refine ⟨10520297303772364357937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1795464073177150183754581 10520297303772364357937)
            ·
              rfl

theorem cell22_2489317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 9].length) (baseStart_2489317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489317 prefixEnd_2489317 := by exact prefixLift 2489317
  have htrace : WordTrace (prefixWord ++ tailWord_2489317) baseStart_2489317 baseEnd_2489317 := by
    simpa [prefixWord, tailWord_2489317, baseEnd_2489317] using wordTrace_append hprefix tailTrace_2489317
  have hstable : (prefixWord ++ tailWord_2489317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489317).length < 2 ^ (prefixWord ++ tailWord_2489317).sum := by decide
  have hdescent : baseEnd_2489317 < baseStart_2489317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489396 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2489396 : Nat := 118140960795 + 2489396 * 2 ^ 59
def prefixEnd_2489396 : Nat := 4983230072969 + 3 ^ 40 * 2489396 * 2
def baseEnd_2489396 : Nat := 284057041640010546755885

theorem tailTrace_2489396 : CollatzResearch.WordTrace tailWord_2489396 prefixEnd_2489396 284057041640010546755885 := by
  unfold tailWord_2489396
  simp only [CollatzResearch.WordTrace]
  refine ⟨45397865644675460916796021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60530487526233947889061361 45397865644675460916796021)
  ·
    refine ⟨4256049904188324460949627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45397865644675460916796021 4256049904188324460949627)
    ·
      refine ⟨6384074856282486691424441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256049904188324460949627 6384074856282486691424441)
      ·
        refine ⟨4788056142211865018568331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384074856282486691424441 4788056142211865018568331)
        ·
          refine ⟨7182084213317797527852497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788056142211865018568331 7182084213317797527852497)
          ·
            refine ⟨5386563159988348145889373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7182084213317797527852497 5386563159988348145889373)
            ·
              refine ⟨2019961184995630554708515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5386563159988348145889373 2019961184995630554708515)
              ·
                refine ⟨3029941777493445832062773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019961184995630554708515 3029941777493445832062773)
                ·
                  refine ⟨284057041640010546755885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029941777493445832062773 284057041640010546755885)
                  ·
                    rfl

theorem cell22_2489396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2489396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489396 prefixEnd_2489396 := by exact prefixLift 2489396
  have htrace : WordTrace (prefixWord ++ tailWord_2489396) baseStart_2489396 baseEnd_2489396 := by
    simpa [prefixWord, tailWord_2489396, baseEnd_2489396] using wordTrace_append hprefix tailTrace_2489396
  have hstable : (prefixWord ++ tailWord_2489396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489396).length < 2 ^ (prefixWord ++ tailWord_2489396).sum := by decide
  have hdescent : baseEnd_2489396 < baseStart_2489396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489422 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2489422 : Nat := 118140960795 + 2489422 * 2 ^ 59
def prefixEnd_2489422 : Nat := 4983230072969 + 3 ^ 40 * 2489422 * 2
def baseEnd_2489422 : Nat := 852180025251376239117575

theorem tailTrace_2489422 : CollatzResearch.WordTrace tailWord_2489422 prefixEnd_2489422 852180025251376239117575 := by
  unfold tailWord_2489422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349584948407091034254815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60531119724837818849359013 11349584948407091034254815)
  ·
    refine ⟨17024377422610636551382223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11349584948407091034254815 17024377422610636551382223)
    ·
      refine ⟨25536566133915954827073335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17024377422610636551382223 25536566133915954827073335)
      ·
        refine ⟨38304849200873932240610003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25536566133915954827073335 38304849200873932240610003)
        ·
          refine ⟨57457273801310898360915005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38304849200873932240610003 57457273801310898360915005)
          ·
            refine ⟨21546477675491586885343127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57457273801310898360915005 21546477675491586885343127)
            ·
              refine ⟨32319716513237380328014691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21546477675491586885343127 32319716513237380328014691)
              ·
                refine ⟨48479574769856070492022037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32319716513237380328014691 48479574769856070492022037)
                ·
                  refine ⟨2272480067337003304313533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48479574769856070492022037 2272480067337003304313533)
                  ·
                    refine ⟨852180025251376239117575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272480067337003304313533 852180025251376239117575)
                    ·
                      rfl

theorem cell22_2489422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2489422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489422 prefixEnd_2489422 := by exact prefixLift 2489422
  have htrace : WordTrace (prefixWord ++ tailWord_2489422) baseStart_2489422 baseEnd_2489422 := by
    simpa [prefixWord, tailWord_2489422, baseEnd_2489422] using wordTrace_append hprefix tailTrace_2489422
  have hstable : (prefixWord ++ tailWord_2489422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489422).length < 2 ^ (prefixWord ++ tailWord_2489422).sum := by decide
  have hdescent : baseEnd_2489422 < baseStart_2489422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489467 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 3, 3]
def baseStart_2489467 : Nat := 118140960795 + 2489467 * 2 ^ 59
def prefixEnd_2489467 : Nat := 4983230072969 + 3 ^ 40 * 2489467 * 2
def baseEnd_2489467 : Nat := 852195429671011121742437

theorem tailTrace_2489467 : CollatzResearch.WordTrace tailWord_2489467 prefixEnd_2489467 852195429671011121742437 := by
  unfold tailWord_2489467
  simp only [CollatzResearch.WordTrace]
  refine ⟨90798320872093700959426655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60532213914729133972951103 90798320872093700959426655)
  ·
    refine ⟨136197481308140551439139983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90798320872093700959426655 136197481308140551439139983)
    ·
      refine ⟨204296221962210827158709975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136197481308140551439139983 204296221962210827158709975)
      ·
        refine ⟨306444332943316240738064963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204296221962210827158709975 306444332943316240738064963)
        ·
          refine ⟨459666499414974361107097445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306444332943316240738064963 459666499414974361107097445)
          ·
            refine ⟨86187468640307692707580771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 459666499414974361107097445 86187468640307692707580771)
            ·
              refine ⟨129281202960461539061371157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86187468640307692707580771 129281202960461539061371157)
              ·
                refine ⟨6060056388771634643501773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129281202960461539061371157 6060056388771634643501773)
                ·
                  refine ⟨2272521145789362991313165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6060056388771634643501773 2272521145789362991313165)
                  ·
                    refine ⟨852195429671011121742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272521145789362991313165 852195429671011121742437)
                    ·
                      rfl

theorem cell22_2489467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].length) (baseStart_2489467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489467 prefixEnd_2489467 := by exact prefixLift 2489467
  have htrace : WordTrace (prefixWord ++ tailWord_2489467) baseStart_2489467 baseEnd_2489467 := by
    simpa [prefixWord, tailWord_2489467, baseEnd_2489467] using wordTrace_append hprefix tailTrace_2489467
  have hstable : (prefixWord ++ tailWord_2489467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489467).length < 2 ^ (prefixWord ++ tailWord_2489467).sum := by decide
  have hdescent : baseEnd_2489467 < baseStart_2489467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489501 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2489501 : Nat := 118140960795 + 2489501 * 2 ^ 59
def prefixEnd_2489501 : Nat := 4983230072969 + 3 ^ 40 * 2489501 * 2
def baseEnd_2489501 : Nat := 852207068565846366392333

theorem tailTrace_2489501 : CollatzResearch.WordTrace tailWord_2489501 prefixEnd_2489501 852207068565846366392333 := by
  unfold tailWord_2489501
  simp only [CollatzResearch.WordTrace]
  refine ⟨90799560953970524766164357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60533040635980349844109571 90799560953970524766164357)
  ·
    refine ⟨17024917678869473393655817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90799560953970524766164357 17024917678869473393655817)
    ·
      refine ⟨12768688259152105045241863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17024917678869473393655817 12768688259152105045241863)
      ·
        refine ⟨19153032388728157567862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12768688259152105045241863 19153032388728157567862795)
        ·
          refine ⟨28729548583092236351794193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19153032388728157567862795 28729548583092236351794193)
          ·
            refine ⟨21547161437319177263845645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28729548583092236351794193 21547161437319177263845645)
            ·
              refine ⟨8080185538994691473942117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21547161437319177263845645 8080185538994691473942117)
              ·
                refine ⟨1515034788561504651364147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8080185538994691473942117 1515034788561504651364147)
                ·
                  refine ⟨2272552182842256977046221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515034788561504651364147 2272552182842256977046221)
                  ·
                    refine ⟨852207068565846366392333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272552182842256977046221 852207068565846366392333)
                    ·
                      rfl

theorem cell22_2489501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2489501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489501 prefixEnd_2489501 := by exact prefixLift 2489501
  have htrace : WordTrace (prefixWord ++ tailWord_2489501) baseStart_2489501 baseEnd_2489501 := by
    simpa [prefixWord, tailWord_2489501, baseEnd_2489501] using wordTrace_append hprefix tailTrace_2489501
  have hstable : (prefixWord ++ tailWord_2489501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489501).length < 2 ^ (prefixWord ++ tailWord_2489501).sum := by decide
  have hdescent : baseEnd_2489501 < baseStart_2489501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489527 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2489527 : Nat := 118140960795 + 2489527 * 2 ^ 59
def prefixEnd_2489527 : Nat := 4983230072969 + 3 ^ 40 * 2489527 * 2
def baseEnd_2489527 : Nat := 852215968897190965242253

theorem tailTrace_2489527 : CollatzResearch.WordTrace tailWord_2489527 prefixEnd_2489527 852215968897190965242253 := by
  unfold tailWord_2489527
  simp only [CollatzResearch.WordTrace]
  refine ⟨90800509251876331206610835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60533672834584220804407223 90800509251876331206610835)
  ·
    refine ⟨136200763877814496809916253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90800509251876331206610835 136200763877814496809916253)
    ·
      refine ⟨51075286454180436303718595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136200763877814496809916253 51075286454180436303718595)
      ·
        refine ⟨76612929681270654455577893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51075286454180436303718595 76612929681270654455577893)
        ·
          refine ⟨14364924315238247710420855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76612929681270654455577893 14364924315238247710420855)
          ·
            refine ⟨21547386472857371565631283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14364924315238247710420855 21547386472857371565631283)
            ·
              refine ⟨32321079709286057348446925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21547386472857371565631283 32321079709286057348446925)
              ·
                refine ⟨12120404890982271505667597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32321079709286057348446925 12120404890982271505667597)
                ·
                  refine ⟨4545151834118351814625349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12120404890982271505667597 4545151834118351814625349)
                  ·
                    refine ⟨852215968897190965242253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4545151834118351814625349 852215968897190965242253)
                    ·
                      rfl

theorem cell22_2489527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2489527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489527 prefixEnd_2489527 := by exact prefixLift 2489527
  have htrace : WordTrace (prefixWord ++ tailWord_2489527) baseStart_2489527 baseEnd_2489527 := by
    simpa [prefixWord, tailWord_2489527, baseEnd_2489527] using wordTrace_append hprefix tailTrace_2489527
  have hstable : (prefixWord ++ tailWord_2489527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489527).length < 2 ^ (prefixWord ++ tailWord_2489527).sum := by decide
  have hdescent : baseEnd_2489527 < baseStart_2489527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489559 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 4]
def baseStart_2489559 : Nat := 118140960795 + 2489559 * 2 ^ 59
def prefixEnd_2489559 : Nat := 4983230072969 + 3 ^ 40 * 2489559 * 2
def baseEnd_2489559 : Nat := 284075641050384516147385

theorem tailTrace_2489559 : CollatzResearch.WordTrace tailWord_2489559 prefixEnd_2489559 284075641050384516147385 := by
  unfold tailWord_2489559
  simp only [CollatzResearch.WordTrace]
  refine ⟨90801676387760400671775731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60534450925173600447850487 90801676387760400671775731)
  ·
    refine ⟨136202514581640601007663597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90801676387760400671775731 136202514581640601007663597)
    ·
      refine ⟨51075942968115225377873849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136202514581640601007663597 51075942968115225377873849)
      ·
        refine ⟨38306957226086419033405387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51075942968115225377873849 38306957226086419033405387)
        ·
          refine ⟨57460435839129628550108081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38306957226086419033405387 57460435839129628550108081)
          ·
            refine ⟨43095326879347221412581061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57460435839129628550108081 43095326879347221412581061)
            ·
              refine ⟨8080373789877604014858949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43095326879347221412581061 8080373789877604014858949)
              ·
                refine ⟨1515070085602050752786053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8080373789877604014858949 1515070085602050752786053)
                ·
                  refine ⟨284075641050384516147385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515070085602050752786053 284075641050384516147385)
                  ·
                    rfl

theorem cell22_2489559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 4].length) (baseStart_2489559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489559 prefixEnd_2489559 := by exact prefixLift 2489559
  have htrace : WordTrace (prefixWord ++ tailWord_2489559) baseStart_2489559 baseEnd_2489559 := by
    simpa [prefixWord, tailWord_2489559, baseEnd_2489559] using wordTrace_append hprefix tailTrace_2489559
  have hstable : (prefixWord ++ tailWord_2489559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489559).length < 2 ^ (prefixWord ++ tailWord_2489559).sum := by decide
  have hdescent : baseEnd_2489559 < baseStart_2489559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489572 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2489572 : Nat := 118140960795 + 2489572 * 2 ^ 59
def prefixEnd_2489572 : Nat := 4983230072969 + 3 ^ 40 * 2489572 * 2
def baseEnd_2489572 : Nat := 852231373316825847867115

theorem tailTrace_2489572 : CollatzResearch.WordTrace tailWord_2489572 prefixEnd_2489572 852231373316825847867115 := by
  unfold tailWord_2489572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45401075268356651945999485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60534767024475535927999313 45401075268356651945999485)
  ·
    refine ⟨17025403225633744479749807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45401075268356651945999485 17025403225633744479749807)
    ·
      refine ⟨25538104838450616719624711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17025403225633744479749807 25538104838450616719624711)
      ·
        refine ⟨38307157257675925079437067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25538104838450616719624711 38307157257675925079437067)
        ·
          refine ⟨57460735886513887619155601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38307157257675925079437067 57460735886513887619155601)
          ·
            refine ⟨43095551914885415714366701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57460735886513887619155601 43095551914885415714366701)
            ·
              refine ⟨16160831968082030892887513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43095551914885415714366701 16160831968082030892887513)
              ·
                refine ⟨12120623976061523169665635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16160831968082030892887513 12120623976061523169665635)
                ·
                  refine ⟨18180935964092284754498453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12120623976061523169665635 18180935964092284754498453)
                  ·
                    refine ⟨852231373316825847867115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18180935964092284754498453 852231373316825847867115)
                    ·
                      rfl

theorem cell22_2489572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2489572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489572 prefixEnd_2489572 := by exact prefixLift 2489572
  have htrace : WordTrace (prefixWord ++ tailWord_2489572) baseStart_2489572 baseEnd_2489572 := by
    simpa [prefixWord, tailWord_2489572, baseEnd_2489572] using wordTrace_append hprefix tailTrace_2489572
  have hstable : (prefixWord ++ tailWord_2489572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489572).length < 2 ^ (prefixWord ++ tailWord_2489572).sum := by decide
  have hdescent : baseEnd_2489572 < baseStart_2489572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489587 : List Nat := [1, 1, 1, 2, 2, 6, 1, 8]
def baseStart_2489587 : Nat := 118140960795 + 2489587 * 2 ^ 59
def prefixEnd_2489587 : Nat := 4983230072969 + 3 ^ 40 * 2489587 * 2
def baseEnd_2489587 : Nat := 94692945347041200971341

theorem tailTrace_2489587 : CollatzResearch.WordTrace tailWord_2489587 prefixEnd_2489587 94692945347041200971341 := by
  unfold tailWord_2489587
  simp only [CollatzResearch.WordTrace]
  refine ⟨90802697631658961453795015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60535131754439307635863343 90802697631658961453795015)
  ·
    refine ⟨136204046447488442180692523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90802697631658961453795015 136204046447488442180692523)
    ·
      refine ⟨204306069671232663271038785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136204046447488442180692523 204306069671232663271038785)
      ·
        refine ⟨153229552253424497453279089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204306069671232663271038785 153229552253424497453279089)
        ·
          refine ⟨114922164190068373089959317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153229552253424497453279089 114922164190068373089959317)
          ·
            refine ⟨5386976446409454988591843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114922164190068373089959317 5386976446409454988591843)
            ·
              refine ⟨8080464669614182482887765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386976446409454988591843 8080464669614182482887765)
              ·
                refine ⟨94692945347041200971341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8080464669614182482887765 94692945347041200971341)
                ·
                  rfl

theorem cell22_2489587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_2489587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489587 prefixEnd_2489587 := by exact prefixLift 2489587
  have htrace : WordTrace (prefixWord ++ tailWord_2489587) baseStart_2489587 baseEnd_2489587 := by
    simpa [prefixWord, tailWord_2489587, baseEnd_2489587] using wordTrace_append hprefix tailTrace_2489587
  have hstable : (prefixWord ++ tailWord_2489587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489587).length < 2 ^ (prefixWord ++ tailWord_2489587).sum := by decide
  have hdescent : baseEnd_2489587 < baseStart_2489587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489604 : List Nat := [2, 3, 2, 2, 2, 3, 8]
def baseStart_2489604 : Nat := 118140960795 + 2489604 * 2 ^ 59
def prefixEnd_2489604 : Nat := 4983230072969 + 3 ^ 40 * 2489604 * 2
def baseEnd_2489604 : Nat := 31564530650769941891371

theorem tailTrace_2489604 : CollatzResearch.WordTrace tailWord_2489604 prefixEnd_2489604 31564530650769941891371 := by
  unfold tailWord_2489604
  simp only [CollatzResearch.WordTrace]
  refine ⟨45401658836298686678581933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60535545115064915571442577 45401658836298686678581933)
  ·
    refine ⟨17025622063612007504468225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45401658836298686678581933 17025622063612007504468225)
    ·
      refine ⟨12769216547709005628351169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17025622063612007504468225 12769216547709005628351169)
      ·
        refine ⟨9576912410781754221263377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12769216547709005628351169 9576912410781754221263377)
        ·
          refine ⟨7182684308086315665947533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9576912410781754221263377 7182684308086315665947533)
          ·
            refine ⟨2693506615532368374730325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7182684308086315665947533 2693506615532368374730325)
            ·
              refine ⟨31564530650769941891371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2693506615532368374730325 31564530650769941891371)
              ·
                rfl

theorem cell22_2489604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 8].length) (baseStart_2489604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489604 prefixEnd_2489604 := by exact prefixLift 2489604
  have htrace : WordTrace (prefixWord ++ tailWord_2489604) baseStart_2489604 baseEnd_2489604 := by
    simpa [prefixWord, tailWord_2489604, baseEnd_2489604] using wordTrace_append hprefix tailTrace_2489604
  have hstable : (prefixWord ++ tailWord_2489604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489604).length < 2 ^ (prefixWord ++ tailWord_2489604).sum := by decide
  have hdescent : baseEnd_2489604 < baseStart_2489604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489617 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2489617 : Nat := 118140960795 + 2489617 * 2 ^ 59
def prefixEnd_2489617 : Nat := 4983230072969 + 3 ^ 40 * 2489617 * 2
def baseEnd_2489617 : Nat := 852246777736460730491977

theorem tailTrace_2489617 : CollatzResearch.WordTrace tailWord_2489617 prefixEnd_2489617 852246777736460730491977 := by
  unfold tailWord_2489617
  simp only [CollatzResearch.WordTrace]
  refine ⟨90803791821550276577387105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60535861214366851051591403 90803791821550276577387105)
  ·
    refine ⟨68102843866162707433040329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90803791821550276577387105 68102843866162707433040329)
    ·
      refine ⟨51077132899622030574780247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68102843866162707433040329 51077132899622030574780247)
      ·
        refine ⟨76615699349433045862170371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51077132899622030574780247 76615699349433045862170371)
        ·
          refine ⟨114923549024149568793255557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76615699349433045862170371 114923549024149568793255557)
          ·
            refine ⟨21548165442028044148735417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114923549024149568793255557 21548165442028044148735417)
            ·
              refine ⟨16161124081521033111551563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21548165442028044148735417 16161124081521033111551563)
              ·
                refine ⟨24241686122281549667327345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16161124081521033111551563 24241686122281549667327345)
                ·
                  refine ⟨18181264591711162250495509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24241686122281549667327345 18181264591711162250495509)
                  ·
                    refine ⟨852246777736460730491977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18181264591711162250495509 852246777736460730491977)
                    ·
                      rfl

theorem cell22_2489617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2489617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489617 prefixEnd_2489617 := by exact prefixLift 2489617
  have htrace : WordTrace (prefixWord ++ tailWord_2489617) baseStart_2489617 baseEnd_2489617 := by
    simpa [prefixWord, tailWord_2489617, baseEnd_2489617] using wordTrace_append hprefix tailTrace_2489617
  have hstable : (prefixWord ++ tailWord_2489617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489617).length < 2 ^ (prefixWord ++ tailWord_2489617).sum := by decide
  have hdescent : baseEnd_2489617 < baseStart_2489617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489647 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_2489647 : Nat := 118140960795 + 2489647 * 2 ^ 59
def prefixEnd_2489647 : Nat := 4983230072969 + 3 ^ 40 * 2489647 * 2
def baseEnd_2489647 : Nat := 852257047349550652241885

theorem tailTrace_2489647 : CollatzResearch.WordTrace tailWord_2489647 prefixEnd_2489647 852257047349550652241885 := by
  unfold tailWord_2489647
  simp only [CollatzResearch.WordTrace]
  refine ⟨90804886011441591700979195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60536590674294394467319463 90804886011441591700979195)
  ·
    refine ⟨136207329017162387551468793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90804886011441591700979195 136207329017162387551468793)
    ·
      refine ⟨102155496762871790663601595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136207329017162387551468793 102155496762871790663601595)
      ·
        refine ⟨153233245144307685995402393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102155496762871790663601595 153233245144307685995402393)
        ·
          refine ⟨114924933858230764496551795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153233245144307685995402393 114924933858230764496551795)
          ·
            refine ⟨172387400787346146744827693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114924933858230764496551795 172387400787346146744827693)
            ·
              refine ⟨64645275295254805029310385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172387400787346146744827693 64645275295254805029310385)
              ·
                refine ⟨48483956471441103771982789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64645275295254805029310385 48483956471441103771982789)
                ·
                  refine ⟨9090741838395206957246773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48483956471441103771982789 9090741838395206957246773)
                  ·
                    refine ⟨852257047349550652241885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9090741838395206957246773 852257047349550652241885)
                    ·
                      rfl

theorem cell22_2489647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_2489647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489647 prefixEnd_2489647 := by exact prefixLift 2489647
  have htrace : WordTrace (prefixWord ++ tailWord_2489647) baseStart_2489647 baseEnd_2489647 := by
    simpa [prefixWord, tailWord_2489647, baseEnd_2489647] using wordTrace_append hprefix tailTrace_2489647
  have hstable : (prefixWord ++ tailWord_2489647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489647).length < 2 ^ (prefixWord ++ tailWord_2489647).sum := by decide
  have hdescent : baseEnd_2489647 < baseStart_2489647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489711 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 4]
def baseStart_2489711 : Nat := 118140960795 + 2489711 * 2 ^ 59
def prefixEnd_2489711 : Nat := 4983230072969 + 3 ^ 40 * 2489711 * 2
def baseEnd_2489711 : Nat := 284092985285825272880563

theorem tailTrace_2489711 : CollatzResearch.WordTrace tailWord_2489711 prefixEnd_2489711 284092985285825272880563 := by
  unfold tailWord_2489711
  simp only [CollatzResearch.WordTrace]
  refine ⟨90807220283209730631308987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60538146855473153754205991 90807220283209730631308987)
  ·
    refine ⟨136210830424814595946963481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90807220283209730631308987 136210830424814595946963481)
    ·
      refine ⟨102158122818610946960222611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136210830424814595946963481 102158122818610946960222611)
      ·
        refine ⟨153237184227916420440333917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102158122818610946960222611 153237184227916420440333917)
        ·
          refine ⟨57463944085468657665125219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153237184227916420440333917 57463944085468657665125219)
          ·
            refine ⟨86195916128202986497687829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57463944085468657665125219 86195916128202986497687829)
            ·
              refine ⟨4040433568509514992079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86195916128202986497687829 4040433568509514992079117)
              ·
                refine ⟨1515162588191068122029669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4040433568509514992079117 1515162588191068122029669)
                ·
                  refine ⟨284092985285825272880563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515162588191068122029669 284092985285825272880563)
                  ·
                    rfl

theorem cell22_2489711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 4].length) (baseStart_2489711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489711 prefixEnd_2489711 := by exact prefixLift 2489711
  have htrace : WordTrace (prefixWord ++ tailWord_2489711) baseStart_2489711 baseEnd_2489711 := by
    simpa [prefixWord, tailWord_2489711, baseEnd_2489711] using wordTrace_append hprefix tailTrace_2489711
  have hstable : (prefixWord ++ tailWord_2489711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489711).length < 2 ^ (prefixWord ++ tailWord_2489711).sum := by decide
  have hdescent : baseEnd_2489711 < baseStart_2489711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489724 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2489724 : Nat := 118140960795 + 2489724 * 2 ^ 59
def prefixEnd_2489724 : Nat := 4983230072969 + 3 ^ 40 * 2489724 * 2
def baseEnd_2489724 : Nat := 852283406023148118066649

theorem tailTrace_2489724 : CollatzResearch.WordTrace tailWord_2489724 prefixEnd_2489724 852283406023148118066649 := by
  unfold tailWord_2489724
  simp only [CollatzResearch.WordTrace]
  refine ⟨45403847216081316925766113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60538462954775089234354817 45403847216081316925766113)
  ·
    refine ⟨34052885412060987694324585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45403847216081316925766113 34052885412060987694324585)
    ·
      refine ⟨25539664059045740770743439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34052885412060987694324585 25539664059045740770743439)
      ·
        refine ⟨38309496088568611156115159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25539664059045740770743439 38309496088568611156115159)
        ·
          refine ⟨57464244132852916734172739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38309496088568611156115159 57464244132852916734172739)
          ·
            refine ⟨86196366199279375101259109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57464244132852916734172739 86196366199279375101259109)
            ·
              refine ⟨16161818662364882831486083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86196366199279375101259109 16161818662364882831486083)
              ·
                refine ⟨24242727993547324247229125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16161818662364882831486083 24242727993547324247229125)
                ·
                  refine ⟨4545511498790123296355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24242727993547324247229125 4545511498790123296355461)
                  ·
                    refine ⟨852283406023148118066649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4545511498790123296355461 852283406023148118066649)
                    ·
                      rfl

theorem cell22_2489724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2489724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489724 prefixEnd_2489724 := by exact prefixLift 2489724
  have htrace : WordTrace (prefixWord ++ tailWord_2489724) baseStart_2489724 baseEnd_2489724 := by
    simpa [prefixWord, tailWord_2489724, baseEnd_2489724] using wordTrace_append hprefix tailTrace_2489724
  have hstable : (prefixWord ++ tailWord_2489724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489724).length < 2 ^ (prefixWord ++ tailWord_2489724).sum := by decide
  have hdescent : baseEnd_2489724 < baseStart_2489724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489754 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2489754 : Nat := 118140960795 + 2489754 * 2 ^ 59
def prefixEnd_2489754 : Nat := 4983230072969 + 3 ^ 40 * 2489754 * 2
def baseEnd_2489754 : Nat := 852293675636238039816557

theorem tailTrace_2489754 : CollatzResearch.WordTrace tailWord_2489754 prefixEnd_2489754 852293675636238039816557 := by
  unfold tailWord_2489754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702197155513487243781079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60539192414702632650082877 22702197155513487243781079)
  ·
    refine ⟨34053295733270230865671619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22702197155513487243781079 34053295733270230865671619)
    ·
      refine ⟨51079943599905346298507429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34053295733270230865671619 51079943599905346298507429)
      ·
        refine ⟨9577489424982252430970143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51079943599905346298507429 9577489424982252430970143)
        ·
          refine ⟨14366234137473378646455215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577489424982252430970143 14366234137473378646455215)
          ·
            refine ⟨21549351206210067969682823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14366234137473378646455215 21549351206210067969682823)
            ·
              refine ⟨32324026809315101954524235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21549351206210067969682823 32324026809315101954524235)
              ·
                refine ⟨48486040213972652931786353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32324026809315101954524235 48486040213972652931786353)
                ·
                  refine ⟨36364530160479489698839765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48486040213972652931786353 36364530160479489698839765)
                  ·
                    refine ⟨852293675636238039816557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36364530160479489698839765 852293675636238039816557)
                    ·
                      rfl

theorem cell22_2489754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2489754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489754 prefixEnd_2489754 := by exact prefixLift 2489754
  have htrace : WordTrace (prefixWord ++ tailWord_2489754) baseStart_2489754 baseEnd_2489754 := by
    simpa [prefixWord, tailWord_2489754, baseEnd_2489754] using wordTrace_append hprefix tailTrace_2489754
  have hstable : (prefixWord ++ tailWord_2489754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489754).length < 2 ^ (prefixWord ++ tailWord_2489754).sum := by decide
  have hdescent : baseEnd_2489754 < baseStart_2489754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489784 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_2489784 : Nat := 118140960795 + 2489784 * 2 ^ 59
def prefixEnd_2489784 : Nat := 4983230072969 + 3 ^ 40 * 2489784 * 2
def baseEnd_2489784 : Nat := 284101315083109320522155

theorem tailTrace_2489784 : CollatzResearch.WordTrace tailWord_2489784 prefixEnd_2489784 284101315083109320522155 := by
  unfold tailWord_2489784
  simp only [CollatzResearch.WordTrace]
  refine ⟨45404941405972632049358203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60539921874630176065810937 45404941405972632049358203)
  ·
    refine ⟨68107412108958948074037305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45404941405972632049358203 68107412108958948074037305)
    ·
      refine ⟨51080559081719211055527979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68107412108958948074037305 51080559081719211055527979)
      ·
        refine ⟨76620838622578816583291969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51080559081719211055527979 76620838622578816583291969)
        ·
          refine ⟨57465628966934112437468977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76620838622578816583291969 57465628966934112437468977)
          ·
            refine ⟨43099221725200584328101733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57465628966934112437468977 43099221725200584328101733)
            ·
              refine ⟨8081104073475109561519075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43099221725200584328101733 8081104073475109561519075)
              ·
                refine ⟨12121656110212664342278613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081104073475109561519075 12121656110212664342278613)
                ·
                  refine ⟨284101315083109320522155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12121656110212664342278613 284101315083109320522155)
                  ·
                    rfl

theorem cell22_2489784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_2489784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489784 prefixEnd_2489784 := by exact prefixLift 2489784
  have htrace : WordTrace (prefixWord ++ tailWord_2489784) baseStart_2489784 baseEnd_2489784 := by
    simpa [prefixWord, tailWord_2489784, baseEnd_2489784] using wordTrace_append hprefix tailTrace_2489784
  have hstable : (prefixWord ++ tailWord_2489784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489784).length < 2 ^ (prefixWord ++ tailWord_2489784).sum := by decide
  have hdescent : baseEnd_2489784 < baseStart_2489784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489799 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2489799 : Nat := 118140960795 + 2489799 * 2 ^ 59
def prefixEnd_2489799 : Nat := 4983230072969 + 3 ^ 40 * 2489799 * 2
def baseEnd_2489799 : Nat := 852309080055872922441419

theorem tailTrace_2489799 : CollatzResearch.WordTrace tailWord_2489799 prefixEnd_2489799 852309080055872922441419 := by
  unfold tailWord_2489799
  simp only [CollatzResearch.WordTrace]
  refine ⟨90810429906890921660512451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60540286604593947773674967 90810429906890921660512451)
  ·
    refine ⟨136215644860336382490768677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90810429906890921660512451 136215644860336382490768677)
    ·
      refine ⟨25540433411313071717019127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136215644860336382490768677 25540433411313071717019127)
      ·
        refine ⟨38310650116969607575528691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25540433411313071717019127 38310650116969607575528691)
        ·
          refine ⟨57465975175454411363293037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38310650116969607575528691 57465975175454411363293037)
          ·
            refine ⟨21549740690795404261234889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57465975175454411363293037 21549740690795404261234889)
            ·
              refine ⟨16162305518096553195926167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21549740690795404261234889 16162305518096553195926167)
              ·
                refine ⟨24243458277144829793889251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16162305518096553195926167 24243458277144829793889251)
                ·
                  refine ⟨36365187415717244690833877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24243458277144829793889251 36365187415717244690833877)
                  ·
                    refine ⟨852309080055872922441419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36365187415717244690833877 852309080055872922441419)
                    ·
                      rfl

theorem cell22_2489799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2489799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489799 prefixEnd_2489799 := by exact prefixLift 2489799
  have htrace : WordTrace (prefixWord ++ tailWord_2489799) baseStart_2489799 baseEnd_2489799 := by
    simpa [prefixWord, tailWord_2489799, baseEnd_2489799] using wordTrace_append hprefix tailTrace_2489799
  have hstable : (prefixWord ++ tailWord_2489799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489799).length < 2 ^ (prefixWord ++ tailWord_2489799).sum := by decide
  have hdescent : baseEnd_2489799 < baseStart_2489799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489861 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_2489861 : Nat := 118140960795 + 2489861 * 2 ^ 59
def prefixEnd_2489861 : Nat := 4983230072969 + 3 ^ 40 * 2489861 * 2
def baseEnd_2489861 : Nat := 852330303922925427391229

theorem tailTrace_2489861 : CollatzResearch.WordTrace tailWord_2489861 prefixEnd_2489861 852330303922925427391229 := by
  unfold tailWord_2489861
  simp only [CollatzResearch.WordTrace]
  refine ⟨90812691232666306249269437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60541794155110870832846291 90812691232666306249269437)
  ·
    refine ⟨34054759212249864843476039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90812691232666306249269437 34054759212249864843476039)
    ·
      refine ⟨51082138818374797265214059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34054759212249864843476039 51082138818374797265214059)
      ·
        refine ⟨76623208227562195897821089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51082138818374797265214059 76623208227562195897821089)
        ·
          refine ⟨57467406170671646923365817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76623208227562195897821089 57467406170671646923365817)
          ·
            refine ⟨43100554628003735192524363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57467406170671646923365817 43100554628003735192524363)
            ·
              refine ⟨64650831942005602788786545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43100554628003735192524363 64650831942005602788786545)
              ·
                refine ⟨48488123956504202091589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64650831942005602788786545 48488123956504202091589909)
                ·
                  refine ⟨2272880810461134473043277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48488123956504202091589909 2272880810461134473043277)
                  ·
                    refine ⟨852330303922925427391229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272880810461134473043277 852330303922925427391229)
                    ·
                      rfl

theorem cell22_2489861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_2489861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489861 prefixEnd_2489861 := by exact prefixLift 2489861
  have htrace : WordTrace (prefixWord ++ tailWord_2489861) baseStart_2489861 baseEnd_2489861 := by
    simpa [prefixWord, tailWord_2489861, baseEnd_2489861] using wordTrace_append hprefix tailTrace_2489861
  have hstable : (prefixWord ++ tailWord_2489861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489861).length < 2 ^ (prefixWord ++ tailWord_2489861).sum := by decide
  have hdescent : baseEnd_2489861 < baseStart_2489861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489880 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_2489880 : Nat := 118140960795 + 2489880 * 2 ^ 59
def prefixEnd_2489880 : Nat := 4983230072969 + 3 ^ 40 * 2489880 * 2
def baseEnd_2489880 : Nat := 284112269337071903722057

theorem tailTrace_2489880 : CollatzResearch.WordTrace tailWord_2489880 prefixEnd_2489880 284112269337071903722057 := by
  unfold tailWord_2489880
  simp only [CollatzResearch.WordTrace]
  refine ⟨45406692109798736247105547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60542256146398314996140729 45406692109798736247105547)
  ·
    refine ⟨68110038164698104370658321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45406692109798736247105547 68110038164698104370658321)
    ·
      refine ⟨51082528623523578277993741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68110038164698104370658321 51082528623523578277993741)
      ·
        refine ⟨19155948233821341854247653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51082528623523578277993741 19155948233821341854247653)
        ·
          refine ⟨3591740293841501597671435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19155948233821341854247653 3591740293841501597671435)
          ·
            refine ⟨5387610440762252396507153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591740293841501597671435 5387610440762252396507153)
            ·
              refine ⟨4040707830571689297380365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387610440762252396507153 4040707830571689297380365)
              ·
                refine ⟨1515265436464383486517637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4040707830571689297380365 1515265436464383486517637)
                ·
                  refine ⟨284112269337071903722057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515265436464383486517637 284112269337071903722057)
                  ·
                    rfl

theorem cell22_2489880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_2489880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489880 prefixEnd_2489880 := by exact prefixLift 2489880
  have htrace : WordTrace (prefixWord ++ tailWord_2489880) baseStart_2489880 baseEnd_2489880 := by
    simpa [prefixWord, tailWord_2489880, baseEnd_2489880] using wordTrace_append hprefix tailTrace_2489880
  have hstable : (prefixWord ++ tailWord_2489880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489880).length < 2 ^ (prefixWord ++ tailWord_2489880).sum := by decide
  have hdescent : baseEnd_2489880 < baseStart_2489880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489886 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2489886 : Nat := 118140960795 + 2489886 * 2 ^ 59
def prefixEnd_2489886 : Nat := 4983230072969 + 3 ^ 40 * 2489886 * 2
def baseEnd_2489886 : Nat := 284112953977944565172051

theorem tailTrace_2489886 : CollatzResearch.WordTrace tailWord_2489886 prefixEnd_2489886 284112953977944565172051 := by
  unfold tailWord_2489886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351700382196966939866189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60542402038383823679286341 11351700382196966939866189)
  ·
    refine ⟨4256887643323862602449821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11351700382196966939866189 4256887643323862602449821)
    ·
      refine ⟨1596332866246448475918683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4256887643323862602449821 1596332866246448475918683)
      ·
        refine ⟨2394499299369672713878025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596332866246448475918683 2394499299369672713878025)
        ·
          refine ⟨1795874474527254535408519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394499299369672713878025 1795874474527254535408519)
          ·
            refine ⟨2693811711790881803112779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795874474527254535408519 2693811711790881803112779)
            ·
              refine ⟨4040717567686322704669169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693811711790881803112779 4040717567686322704669169)
              ·
                refine ⟨3030538175764742028501877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4040717567686322704669169 3030538175764742028501877)
                ·
                  refine ⟨284112953977944565172051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3030538175764742028501877 284112953977944565172051)
                  ·
                    rfl

theorem cell22_2489886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2489886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489886 prefixEnd_2489886 := by exact prefixLift 2489886
  have htrace : WordTrace (prefixWord ++ tailWord_2489886) baseStart_2489886 baseEnd_2489886 := by
    simpa [prefixWord, tailWord_2489886, baseEnd_2489886] using wordTrace_append hprefix tailTrace_2489886
  have hstable : (prefixWord ++ tailWord_2489886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489886).length < 2 ^ (prefixWord ++ tailWord_2489886).sum := by decide
  have hdescent : baseEnd_2489886 < baseStart_2489886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489891 : List Nat := [1, 1, 1, 4, 5, 1, 9]
def baseStart_2489891 : Nat := 118140960795 + 2489891 * 2 ^ 59
def prefixEnd_2489891 : Nat := 4983230072969 + 3 ^ 40 * 2489891 * 2
def baseEnd_2489891 : Nat := 31568169390222790708931

theorem tailTrace_2489891 : CollatzResearch.WordTrace tailWord_2489891 prefixEnd_2489891 31568169390222790708931 := by
  unfold tailWord_2489891
  simp only [CollatzResearch.WordTrace]
  refine ⟨90813785422557621372861527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60542523615038414248574351 90813785422557621372861527)
  ·
    refine ⟨136220678133836432059292291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90813785422557621372861527 136220678133836432059292291)
    ·
      refine ⟨204331017200754648088938437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136220678133836432059292291 204331017200754648088938437)
      ·
        refine ⟨38312065725141496516675957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204331017200754648088938437 38312065725141496516675957)
        ·
          refine ⟨3591756161732015298438371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38312065725141496516675957 3591756161732015298438371)
          ·
            refine ⟨5387634242598022947657557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591756161732015298438371 5387634242598022947657557)
            ·
              refine ⟨31568169390222790708931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5387634242598022947657557 31568169390222790708931)
              ·
                rfl

theorem cell22_2489891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 9].length) (baseStart_2489891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489891 prefixEnd_2489891 := by exact prefixLift 2489891
  have htrace : WordTrace (prefixWord ++ tailWord_2489891) baseStart_2489891 baseEnd_2489891 := by
    simpa [prefixWord, tailWord_2489891, baseEnd_2489891] using wordTrace_append hprefix tailTrace_2489891
  have hstable : (prefixWord ++ tailWord_2489891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489891).length < 2 ^ (prefixWord ++ tailWord_2489891).sum := by decide
  have hdescent : baseEnd_2489891 < baseStart_2489891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489942 : List Nat := [5, 2, 2, 2, 1, 2, 8]
def baseStart_2489942 : Nat := 118140960795 + 2489942 * 2 ^ 59
def prefixEnd_2489942 : Nat := 4983230072969 + 3 ^ 40 * 2489942 * 2
def baseEnd_2489942 : Nat := 31568815995491415411703

theorem tailTrace_2489942 : CollatzResearch.WordTrace tailWord_2489942 prefixEnd_2489942 31568815995491415411703 := by
  unfold tailWord_2489942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675977846585803567685505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60543763696915238055312053 5675977846585803567685505)
  ·
    refine ⟨4256983384939352675764129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5675977846585803567685505 4256983384939352675764129)
    ·
      refine ⟨3192737538704514506823097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4256983384939352675764129 3192737538704514506823097)
      ·
        refine ⟨2394553154028385880117323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3192737538704514506823097 2394553154028385880117323)
        ·
          refine ⟨3591829731042578820175985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394553154028385880117323 3591829731042578820175985)
          ·
            refine ⟨2693872298281934115131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3591829731042578820175985 2693872298281934115131989)
            ·
              refine ⟨31568815995491415411703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2693872298281934115131989 31568815995491415411703)
              ·
                rfl

theorem cell22_2489942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 8].length) (baseStart_2489942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489942 prefixEnd_2489942 := by exact prefixLift 2489942
  have htrace : WordTrace (prefixWord ++ tailWord_2489942) baseStart_2489942 baseEnd_2489942 := by
    simpa [prefixWord, tailWord_2489942, baseEnd_2489942] using wordTrace_append hprefix tailTrace_2489942
  have hstable : (prefixWord ++ tailWord_2489942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489942).length < 2 ^ (prefixWord ++ tailWord_2489942).sum := by decide
  have hdescent : baseEnd_2489942 < baseStart_2489942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489970 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_2489970 : Nat := 118140960795 + 2489970 * 2 ^ 59
def prefixEnd_2489970 : Nat := 4983230072969 + 3 ^ 40 * 2489970 * 2
def baseEnd_2489970 : Nat := 284122538950161825471965

theorem tailTrace_2489970 : CollatzResearch.WordTrace tailWord_2489970 prefixEnd_2489970 284122538950161825471965 := by
  unfold tailWord_2489970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704166697317854466246841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60544444526180945243324909 22704166697317854466246841)
  ·
    refine ⟨17028125022988390849685131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22704166697317854466246841 17028125022988390849685131)
    ·
      refine ⟨25542187534482586274527697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17028125022988390849685131 25542187534482586274527697)
      ·
        refine ⟨19156640650861939705895773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25542187534482586274527697 19156640650861939705895773)
        ·
          refine ⟨7183740244073227389710915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19156640650861939705895773 7183740244073227389710915)
          ·
            refine ⟨10775610366109841084566373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183740244073227389710915 10775610366109841084566373)
            ·
              refine ⟨2020426943645595203356195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10775610366109841084566373 2020426943645595203356195)
              ·
                refine ⟨3030640415468392805034293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020426943645595203356195 3030640415468392805034293)
                ·
                  refine ⟨284122538950161825471965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3030640415468392805034293 284122538950161825471965)
                  ·
                    rfl

theorem cell22_2489970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_2489970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2489970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2489970 prefixEnd_2489970 := by exact prefixLift 2489970
  have htrace : WordTrace (prefixWord ++ tailWord_2489970) baseStart_2489970 baseEnd_2489970 := by
    simpa [prefixWord, tailWord_2489970, baseEnd_2489970] using wordTrace_append hprefix tailTrace_2489970
  have hstable : (prefixWord ++ tailWord_2489970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489970).length < 2 ^ (prefixWord ++ tailWord_2489970).sum := by decide
  have hdescent : baseEnd_2489970 < baseStart_2489970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490152 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2490152 : Nat := 118140960795 + 2490152 * 2 ^ 59
def prefixEnd_2490152 : Nat := 4983230072969 + 3 ^ 40 * 2490152 * 2
def baseEnd_2490152 : Nat := 852429919169897668365337

theorem tailTrace_2490152 : CollatzResearch.WordTrace tailWord_2490152 prefixEnd_2490152 852429919169897668365337 := by
  unfold tailWord_2490152
  simp only [CollatzResearch.WordTrace]
  refine ⟨45411652437306031474056355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60548869916408041965408473 45411652437306031474056355)
  ·
    refine ⟨68117478655959047211084533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45411652437306031474056355 68117478655959047211084533)
    ·
      refine ⟨6386013623996160676039175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68117478655959047211084533 6386013623996160676039175)
      ·
        refine ⟨9579020435994241014058763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386013623996160676039175 9579020435994241014058763)
        ·
          refine ⟨14368530653991361521088145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9579020435994241014058763 14368530653991361521088145)
          ·
            refine ⟨10776397990493521140816109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14368530653991361521088145 10776397990493521140816109)
            ·
              refine ⟨4041149246435070427806041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10776397990493521140816109 4041149246435070427806041)
              ·
                refine ⟨3030861934826302820854531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4041149246435070427806041 3030861934826302820854531)
                ·
                  refine ⟨4546292902239454231281797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030861934826302820854531 4546292902239454231281797)
                  ·
                    refine ⟨852429919169897668365337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546292902239454231281797 852429919169897668365337)
                    ·
                      rfl

theorem cell22_2490152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2490152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490152 prefixEnd_2490152 := by exact prefixLift 2490152
  have htrace : WordTrace (prefixWord ++ tailWord_2490152) baseStart_2490152 baseEnd_2490152 := by
    simpa [prefixWord, tailWord_2490152, baseEnd_2490152] using wordTrace_append hprefix tailTrace_2490152
  have hstable : (prefixWord ++ tailWord_2490152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490152).length < 2 ^ (prefixWord ++ tailWord_2490152).sum := by decide
  have hdescent : baseEnd_2490152 < baseStart_2490152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490184 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_2490184 : Nat := 118140960795 + 2490184 * 2 ^ 59
def prefixEnd_2490184 : Nat := 4983230072969 + 3 ^ 40 * 2490184 * 2
def baseEnd_2490184 : Nat := 284146957807953417188413

theorem tailTrace_2490184 : CollatzResearch.WordTrace tailWord_2490184 prefixEnd_2490184 284146957807953417188413 := by
  unfold tailWord_2490184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45412236005248066206638803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60549648006997421608851737 45412236005248066206638803)
  ·
    refine ⟨68118354007872099309958205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45412236005248066206638803 68118354007872099309958205)
    ·
      refine ⟨25544382752952037241234327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68118354007872099309958205 25544382752952037241234327)
      ·
        refine ⟨38316574129428055861851491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25544382752952037241234327 38316574129428055861851491)
        ·
          refine ⟨57474861194142083792777237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38316574129428055861851491 57474861194142083792777237)
          ·
            refine ⟨2694134118475410177786433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57474861194142083792777237 2694134118475410177786433)
            ·
              refine ⟨2020600588856557633339825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694134118475410177786433 2020600588856557633339825)
              ·
                refine ⟨1515450441642418225004869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020600588856557633339825 1515450441642418225004869)
                ·
                  refine ⟨284146957807953417188413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515450441642418225004869 284146957807953417188413)
                  ·
                    rfl

theorem cell22_2490184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_2490184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490184 prefixEnd_2490184 := by exact prefixLift 2490184
  have htrace : WordTrace (prefixWord ++ tailWord_2490184) baseStart_2490184 baseEnd_2490184 := by
    simpa [prefixWord, tailWord_2490184, baseEnd_2490184] using wordTrace_append hprefix tailTrace_2490184
  have hstable : (prefixWord ++ tailWord_2490184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490184).length < 2 ^ (prefixWord ++ tailWord_2490184).sum := by decide
  have hdescent : baseEnd_2490184 < baseStart_2490184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490212 : List Nat := [2, 3, 1, 1, 5, 1, 3, 6]
def baseStart_2490212 : Nat := 118140960795 + 2490212 * 2 ^ 59
def prefixEnd_2490212 : Nat := 4983230072969 + 3 ^ 40 * 2490212 * 2
def baseEnd_2490212 : Nat := 94716717599564167985017

theorem tailTrace_2490212 : CollatzResearch.WordTrace tailWord_2490212 prefixEnd_2490212 94716717599564167985017 := by
  unfold tailWord_2490212
  simp only [CollatzResearch.WordTrace]
  refine ⟨45412746627197346597648445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60550328836263128796864593 45412746627197346597648445)
  ·
    refine ⟨17029779985199004974118167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45412746627197346597648445 17029779985199004974118167)
    ·
      refine ⟨25544669977798507461177251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17029779985199004974118167 25544669977798507461177251)
      ·
        refine ⟨38317004966697761191765877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25544669977798507461177251 38317004966697761191765877)
        ·
          refine ⟨3592219215627915111728051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38317004966697761191765877 3592219215627915111728051)
          ·
            refine ⟨5388328823441872667592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592219215627915111728051 5388328823441872667592077)
            ·
              refine ⟨2020623308790702250347029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388328823441872667592077 2020623308790702250347029)
              ·
                refine ⟨94716717599564167985017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2020623308790702250347029 94716717599564167985017)
                ·
                  rfl

theorem cell22_2490212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_2490212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490212 prefixEnd_2490212 := by exact prefixLift 2490212
  have htrace : WordTrace (prefixWord ++ tailWord_2490212) baseStart_2490212 baseEnd_2490212 := by
    simpa [prefixWord, tailWord_2490212, baseEnd_2490212] using wordTrace_append hprefix tailTrace_2490212
  have hstable : (prefixWord ++ tailWord_2490212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490212).length < 2 ^ (prefixWord ++ tailWord_2490212).sum := by decide
  have hdescent : baseEnd_2490212 < baseStart_2490212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490244 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2490244 : Nat := 118140960795 + 2490244 * 2 ^ 59
def prefixEnd_2490244 : Nat := 4983230072969 + 3 ^ 40 * 2490244 * 2
def baseEnd_2490244 : Nat := 852461412650040095065055

theorem tailTrace_2490244 : CollatzResearch.WordTrace tailWord_2490244 prefixEnd_2490244 852461412650040095065055 := by
  unfold tailWord_2490244
  simp only [CollatzResearch.WordTrace]
  refine ⟨45413330195139381330230893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60551106926852508440307857 45413330195139381330230893)
  ·
    refine ⟨17029998823177267998836585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45413330195139381330230893 17029998823177267998836585)
    ·
      refine ⟨12772499117382950999127439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17029998823177267998836585 12772499117382950999127439)
      ·
        refine ⟨19158748676074426498691159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12772499117382950999127439 19158748676074426498691159)
        ·
          refine ⟨28738123014111639748036739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19158748676074426498691159 28738123014111639748036739)
          ·
            refine ⟨43107184521167459622055109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28738123014111639748036739 43107184521167459622055109)
            ·
              refine ⟨8082597097718898679135333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43107184521167459622055109 8082597097718898679135333)
              ·
                refine ⟨1515486955822293502337875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8082597097718898679135333 1515486955822293502337875)
                ·
                  refine ⟨2273230433733440253506813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515486955822293502337875 2273230433733440253506813)
                  ·
                    refine ⟨852461412650040095065055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273230433733440253506813 852461412650040095065055)
                    ·
                      rfl

theorem cell22_2490244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2490244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490244 prefixEnd_2490244 := by exact prefixLift 2490244
  have htrace : WordTrace (prefixWord ++ tailWord_2490244) baseStart_2490244 baseEnd_2490244 := by
    simpa [prefixWord, tailWord_2490244, baseEnd_2490244] using wordTrace_append hprefix tailTrace_2490244
  have hstable : (prefixWord ++ tailWord_2490244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490244).length < 2 ^ (prefixWord ++ tailWord_2490244).sum := by decide
  have hdescent : baseEnd_2490244 < baseStart_2490244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490302 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2490302 : Nat := 118140960795 + 2490302 * 2 ^ 59
def prefixEnd_2490302 : Nat := 4983230072969 + 3 ^ 40 * 2490302 * 2
def baseEnd_2490302 : Nat := 284160422411782425704959

theorem tailTrace_2490302 : CollatzResearch.WordTrace tailWord_2490302 prefixEnd_2490302 284160422411782425704959 := by
  unfold tailWord_2490302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353596978008579820759145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60552517216045759044048773 11353596978008579820759145)
  ·
    refine ⟨8515197733506434865569359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11353596978008579820759145 8515197733506434865569359)
    ·
      refine ⟨12772796600259652298354039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8515197733506434865569359 12772796600259652298354039)
      ·
        refine ⟨19159194900389478447531059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12772796600259652298354039 19159194900389478447531059)
        ·
          refine ⟨28738792350584217671296589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19159194900389478447531059 28738792350584217671296589)
          ·
            refine ⟨10777047131469081626736221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28738792350584217671296589 10777047131469081626736221)
            ·
              refine ⟨4041392674300905610026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10777047131469081626736221 4041392674300905610026083)
              ·
                refine ⟨6062089011451358415039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041392674300905610026083 6062089011451358415039125)
                ·
                  refine ⟨284160422411782425704959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6062089011451358415039125 284160422411782425704959)
                  ·
                    rfl

theorem cell22_2490302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2490302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490302 prefixEnd_2490302 := by exact prefixLift 2490302
  have htrace : WordTrace (prefixWord ++ tailWord_2490302) baseStart_2490302 baseEnd_2490302 := by
    simpa [prefixWord, tailWord_2490302, baseEnd_2490302] using wordTrace_append hprefix tailTrace_2490302
  have hstable : (prefixWord ++ tailWord_2490302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490302).length < 2 ^ (prefixWord ++ tailWord_2490302).sum := by decide
  have hdescent : baseEnd_2490302 < baseStart_2490302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490315 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_2490315 : Nat := 118140960795 + 2490315 * 2 ^ 59
def prefixEnd_2490315 : Nat := 4983230072969 + 3 ^ 40 * 2490315 * 2
def baseEnd_2490315 : Nat := 852485717401019576539837

theorem tailTrace_2490315 : CollatzResearch.WordTrace tailWord_2490315 prefixEnd_2490315 852485717401019576539837 := by
  unfold tailWord_2490315
  simp only [CollatzResearch.WordTrace]
  refine ⟨90829249973021541786296399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60552833315347694524197599 90829249973021541786296399)
  ·
    refine ⟨136243874959532312679444599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90829249973021541786296399 136243874959532312679444599)
    ·
      refine ⟨204365812439298469019166899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136243874959532312679444599 204365812439298469019166899)
      ·
        refine ⟨306548718658947703528750349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204365812439298469019166899 306548718658947703528750349)
        ·
          refine ⟨114955769497105388823281381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306548718658947703528750349 114955769497105388823281381)
          ·
            refine ⟨21554206780707260404365259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114955769497105388823281381 21554206780707260404365259)
            ·
              refine ⟨32331310171060890606547889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21554206780707260404365259 32331310171060890606547889)
              ·
                refine ⟨24248482628295667954910917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32331310171060890606547889 24248482628295667954910917)
                ·
                  refine ⟨4546590492805437741545797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24248482628295667954910917 4546590492805437741545797)
                  ·
                    refine ⟨852485717401019576539837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546590492805437741545797 852485717401019576539837)
                    ·
                      rfl

theorem cell22_2490315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_2490315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490315 prefixEnd_2490315 := by exact prefixLift 2490315
  have htrace : WordTrace (prefixWord ++ tailWord_2490315) baseStart_2490315 baseEnd_2490315 := by
    simpa [prefixWord, tailWord_2490315, baseEnd_2490315] using wordTrace_append hprefix tailTrace_2490315
  have hstable : (prefixWord ++ tailWord_2490315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490315).length < 2 ^ (prefixWord ++ tailWord_2490315).sum := by decide
  have hdescent : baseEnd_2490315 < baseStart_2490315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490338 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2490338 : Nat := 118140960795 + 2490338 * 2 ^ 59
def prefixEnd_2490338 : Nat := 4983230072969 + 3 ^ 40 * 2490338 * 2
def baseEnd_2490338 : Nat := 852493590771055183214767

theorem tailTrace_2490338 : CollatzResearch.WordTrace tailWord_2490338 prefixEnd_2490338 852493590771055183214767 := by
  unfold tailWord_2490338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22707522212984554178595917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60553392567958811142922445 22707522212984554178595917)
  ·
    refine ⟨8515320829869207816973469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22707522212984554178595917 8515320829869207816973469)
    ·
      refine ⟨3193245311200952931365051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8515320829869207816973469 3193245311200952931365051)
      ·
        refine ⟨4789867966801429397047577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193245311200952931365051 4789867966801429397047577)
        ·
          refine ⟨3592400975101072047785683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4789867966801429397047577 3592400975101072047785683)
          ·
            refine ⟨5388601462651608071678525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592400975101072047785683 5388601462651608071678525)
            ·
              refine ⟨2020725548494353026879447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388601462651608071678525 2020725548494353026879447)
              ·
                refine ⟨3031088322741529540319171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020725548494353026879447 3031088322741529540319171)
                ·
                  refine ⟨4546632484112294310478757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031088322741529540319171 4546632484112294310478757)
                  ·
                    refine ⟨852493590771055183214767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546632484112294310478757 852493590771055183214767)
                    ·
                      rfl

theorem cell22_2490338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2490338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490338 prefixEnd_2490338 := by exact prefixLift 2490338
  have htrace : WordTrace (prefixWord ++ tailWord_2490338) baseStart_2490338 baseEnd_2490338 := by
    simpa [prefixWord, tailWord_2490338, baseEnd_2490338] using wordTrace_append hprefix tailTrace_2490338
  have hstable : (prefixWord ++ tailWord_2490338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490338).length < 2 ^ (prefixWord ++ tailWord_2490338).sum := by decide
  have hdescent : baseEnd_2490338 < baseStart_2490338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490353 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 4]
def baseStart_2490353 : Nat := 118140960795 + 2490353 * 2 ^ 59
def prefixEnd_2490353 : Nat := 4983230072969 + 3 ^ 40 * 2490353 * 2
def baseEnd_2490353 : Nat := 284166241859200048029907

theorem tailTrace_2490353 : CollatzResearch.WordTrace tailWord_2490353 prefixEnd_2490353 284166241859200048029907 := by
  unfold tailWord_2490353
  simp only [CollatzResearch.WordTrace]
  refine ⟨90830635946883874276179713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60553757297922582850786475 90830635946883874276179713)
  ·
    refine ⟨68122976960162905707134785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90830635946883874276179713 68122976960162905707134785)
    ·
      refine ⟨51092232720122179280351089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68122976960162905707134785 51092232720122179280351089)
      ·
        refine ⟨38319174540091634460263317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51092232720122179280351089 38319174540091634460263317)
        ·
          refine ⟨1796211306566795365324843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38319174540091634460263317 1796211306566795365324843)
          ·
            refine ⟨2694316959850193047987265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796211306566795365324843 2694316959850193047987265)
            ·
              refine ⟨2020737719887644785990449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694316959850193047987265 2020737719887644785990449)
              ·
                refine ⟨1515553289915733589492837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020737719887644785990449 1515553289915733589492837)
                ·
                  refine ⟨284166241859200048029907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515553289915733589492837 284166241859200048029907)
                  ·
                    rfl

theorem cell22_2490353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_2490353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490353 prefixEnd_2490353 := by exact prefixLift 2490353
  have htrace : WordTrace (prefixWord ++ tailWord_2490353) baseStart_2490353 baseEnd_2490353 := by
    simpa [prefixWord, tailWord_2490353, baseEnd_2490353] using wordTrace_append hprefix tailTrace_2490353
  have hstable : (prefixWord ++ tailWord_2490353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490353).length < 2 ^ (prefixWord ++ tailWord_2490353).sum := by decide
  have hdescent : baseEnd_2490353 < baseStart_2490353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490360 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2490360 : Nat := 118140960795 + 2490360 * 2 ^ 59
def prefixEnd_2490360 : Nat := 4983230072969 + 3 ^ 40 * 2490360 * 2
def baseEnd_2490360 : Nat := 852501121820654459164699

theorem tailTrace_2490360 : CollatzResearch.WordTrace tailWord_2490360 prefixEnd_2490360 852501121820654459164699 := by
  unfold tailWord_2490360
  simp only [CollatzResearch.WordTrace]
  refine ⟨45415445628929257235842267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60553927505239009647789689 45415445628929257235842267)
  ·
    refine ⟨68123168443393885853763401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45415445628929257235842267 68123168443393885853763401)
    ·
      refine ⟨51092376332545414390322551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68123168443393885853763401 51092376332545414390322551)
      ·
        refine ⟨76638564498818121585483827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51092376332545414390322551 76638564498818121585483827)
        ·
          refine ⟨114957846748227182378225741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76638564498818121585483827 114957846748227182378225741)
          ·
            refine ⟨43109192530585193391834653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114957846748227182378225741 43109192530585193391834653)
            ·
              refine ⟨16165947198969447521937995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43109192530585193391834653 16165947198969447521937995)
              ·
                refine ⟨24248920798454171282906993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16165947198969447521937995 24248920798454171282906993)
                ·
                  refine ⟨18186690598840628462180245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24248920798454171282906993 18186690598840628462180245)
                  ·
                    refine ⟨852501121820654459164699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18186690598840628462180245 852501121820654459164699)
                    ·
                      rfl

theorem cell22_2490360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2490360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490360 prefixEnd_2490360 := by exact prefixLift 2490360
  have htrace : WordTrace (prefixWord ++ tailWord_2490360) baseStart_2490360 baseEnd_2490360 := by
    simpa [prefixWord, tailWord_2490360, baseEnd_2490360] using wordTrace_append hprefix tailTrace_2490360
  have hstable : (prefixWord ++ tailWord_2490360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490360).length < 2 ^ (prefixWord ++ tailWord_2490360).sum := by decide
  have hdescent : baseEnd_2490360 < baseStart_2490360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490396 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2490396 : Nat := 118140960795 + 2490396 * 2 ^ 59
def prefixEnd_2490396 : Nat := 4983230072969 + 3 ^ 40 * 2490396 * 2
def baseEnd_2490396 : Nat := 852513445356362365264589

theorem tailTrace_2490396 : CollatzResearch.WordTrace tailWord_2490396 prefixEnd_2490396 852513445356362365264589 := by
  unfold tailWord_2490396
  simp only [CollatzResearch.WordTrace]
  refine ⟨45416102142864046309997521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60554802857152061746663361 45416102142864046309997521)
  ·
    refine ⟨34062076607148034732498141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45416102142864046309997521 34062076607148034732498141)
    ·
      refine ⟨12773278727680513024686803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34062076607148034732498141 12773278727680513024686803)
      ·
        refine ⟨19159918091520769537030205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773278727680513024686803 19159918091520769537030205)
        ·
          refine ⟨7184969284320288576386327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19159918091520769537030205 7184969284320288576386327)
          ·
            refine ⟨10777453926480432864579491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184969284320288576386327 10777453926480432864579491)
            ·
              refine ⟨16166180889720649296869237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10777453926480432864579491 16166180889720649296869237)
              ·
                refine ⟨1515579458411310871581491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16166180889720649296869237 1515579458411310871581491)
                ·
                  refine ⟨2273369187616966307372237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515579458411310871581491 2273369187616966307372237)
                  ·
                    refine ⟨852513445356362365264589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273369187616966307372237 852513445356362365264589)
                    ·
                      rfl

theorem cell22_2490396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2490396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490396 prefixEnd_2490396 := by exact prefixLift 2490396
  have htrace : WordTrace (prefixWord ++ tailWord_2490396) baseStart_2490396 baseEnd_2490396 := by
    simpa [prefixWord, tailWord_2490396, baseEnd_2490396] using wordTrace_append hprefix tailTrace_2490396
  have hstable : (prefixWord ++ tailWord_2490396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490396).length < 2 ^ (prefixWord ++ tailWord_2490396).sum := by decide
  have hdescent : baseEnd_2490396 < baseStart_2490396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490439 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2490439 : Nat := 118140960795 + 2490439 * 2 ^ 59
def prefixEnd_2490439 : Nat := 4983230072969 + 3 ^ 40 * 2490439 * 2
def baseEnd_2490439 : Nat := 852528165135124586439457

theorem tailTrace_2490439 : CollatzResearch.WordTrace tailWord_2490439 prefixEnd_2490439 852528165135124586439457 := by
  unfold tailWord_2490439
  simp only [CollatzResearch.WordTrace]
  refine ⟨90833772624572310963810371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60555848416381540642540247 90833772624572310963810371)
  ·
    refine ⟨136250658936858466445715557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90833772624572310963810371 136250658936858466445715557)
    ·
      refine ⟨25546998550660962458571667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136250658936858466445715557 25546998550660962458571667)
      ·
        refine ⟨38320497825991443687857501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25546998550660962458571667 38320497825991443687857501)
        ·
          refine ⟨14370186684746791382946563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38320497825991443687857501 14370186684746791382946563)
          ·
            refine ⟨21555280027120187074419845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14370186684746791382946563 21555280027120187074419845)
            ·
              refine ⟨4041615005085035076453721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21555280027120187074419845 4041615005085035076453721)
              ·
                refine ⟨3031211253813776307340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4041615005085035076453721 3031211253813776307340291)
                ·
                  refine ⟨4546816880720664461010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031211253813776307340291 4546816880720664461010437)
                  ·
                    refine ⟨852528165135124586439457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546816880720664461010437 852528165135124586439457)
                    ·
                      rfl

theorem cell22_2490439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2490439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490439 prefixEnd_2490439 := by exact prefixLift 2490439
  have htrace : WordTrace (prefixWord ++ tailWord_2490439) baseStart_2490439 baseEnd_2490439 := by
    simpa [prefixWord, tailWord_2490439, baseEnd_2490439] using wordTrace_append hprefix tailTrace_2490439
  have hstable : (prefixWord ++ tailWord_2490439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490439).length < 2 ^ (prefixWord ++ tailWord_2490439).sum := by decide
  have hdescent : baseEnd_2490439 < baseStart_2490439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490452 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2490452 : Nat := 118140960795 + 2490452 * 2 ^ 59
def prefixEnd_2490452 : Nat := 4983230072969 + 3 ^ 40 * 2490452 * 2
def baseEnd_2490452 : Nat := 852532615300796885864417

theorem tailTrace_2490452 : CollatzResearch.WordTrace tailWord_2490452 prefixEnd_2490452 852532615300796885864417 := by
  unfold tailWord_2490452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45417123386762607092016805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60556164515683476122689073 45417123386762607092016805)
  ·
    refine ⟨8515710635017988829753151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45417123386762607092016805 8515710635017988829753151)
    ·
      refine ⟨12773565952526983244629727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8515710635017988829753151 12773565952526983244629727)
      ·
        refine ⟨19160348928790474866944591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773565952526983244629727 19160348928790474866944591)
        ·
          refine ⟨28740523393185712300416887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160348928790474866944591 28740523393185712300416887)
          ·
            refine ⟨43110785089778568450625331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28740523393185712300416887 43110785089778568450625331)
            ·
              refine ⟨64666177634667852675937997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43110785089778568450625331 64666177634667852675937997)
              ·
                refine ⟨24249816613000444753476749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64666177634667852675937997 24249816613000444753476749)
                ·
                  refine ⟨9093681229875166782553781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24249816613000444753476749 9093681229875166782553781)
                  ·
                    refine ⟨852532615300796885864417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9093681229875166782553781 852532615300796885864417)
                    ·
                      rfl

theorem cell22_2490452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2490452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490452 prefixEnd_2490452 := by exact prefixLift 2490452
  have htrace : WordTrace (prefixWord ++ tailWord_2490452) baseStart_2490452 baseEnd_2490452 := by
    simpa [prefixWord, tailWord_2490452, baseEnd_2490452] using wordTrace_append hprefix tailTrace_2490452
  have hstable : (prefixWord ++ tailWord_2490452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490452).length < 2 ^ (prefixWord ++ tailWord_2490452).sum := by decide
  have hdescent : baseEnd_2490452 < baseStart_2490452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490467 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_2490467 : Nat := 118140960795 + 2490467 * 2 ^ 59
def prefixEnd_2490467 : Nat := 4983230072969 + 3 ^ 40 * 2490467 * 2
def baseEnd_2490467 : Nat := 852537750107341846739371

theorem tailTrace_2490467 : CollatzResearch.WordTrace tailWord_2490467 prefixEnd_2490467 852537750107341846739371 := by
  unfold tailWord_2490467
  simp only [CollatzResearch.WordTrace]
  refine ⟨90834793868470871745829655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60556529245647247830553103 90834793868470871745829655)
  ·
    refine ⟨136252190802706307618744483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90834793868470871745829655 136252190802706307618744483)
    ·
      refine ⟨204378286204059461428116725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136252190802706307618744483 204378286204059461428116725)
      ·
        refine ⟨19160464331630574508885943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204378286204059461428116725 19160464331630574508885943)
        ·
          refine ⟨28740696497445861763328915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160464331630574508885943 28740696497445861763328915)
          ·
            refine ⟨43111044746168792644993373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28740696497445861763328915 43111044746168792644993373)
            ·
              refine ⟨16166641779813297241872515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43111044746168792644993373 16166641779813297241872515)
              ·
                refine ⟨24249962669719945862808773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16166641779813297241872515 24249962669719945862808773)
                ·
                  refine ⟨4546868000572489849276645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24249962669719945862808773 4546868000572489849276645)
                  ·
                    refine ⟨852537750107341846739371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546868000572489849276645 852537750107341846739371)
                    ·
                      rfl

theorem cell22_2490467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_2490467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490467 prefixEnd_2490467 := by exact prefixLift 2490467
  have htrace : WordTrace (prefixWord ++ tailWord_2490467) baseStart_2490467 baseEnd_2490467 := by
    simpa [prefixWord, tailWord_2490467, baseEnd_2490467] using wordTrace_append hprefix tailTrace_2490467
  have hstable : (prefixWord ++ tailWord_2490467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490467).length < 2 ^ (prefixWord ++ tailWord_2490467).sum := by decide
  have hdescent : baseEnd_2490467 < baseStart_2490467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490469 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2490469 : Nat := 118140960795 + 2490469 * 2 ^ 59
def prefixEnd_2490469 : Nat := 4983230072969 + 3 ^ 40 * 2490469 * 2
def baseEnd_2490469 : Nat := 852538434748214508189365

theorem tailTrace_2490469 : CollatzResearch.WordTrace tailWord_2490469 prefixEnd_2490469 852538434748214508189365 := by
  unfold tailWord_2490469
  simp only [CollatzResearch.WordTrace]
  refine ⟨90834866814463626087402461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60556577876309084058268307 90834866814463626087402461)
  ·
    refine ⟨34063075055423859782775923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90834866814463626087402461 34063075055423859782775923)
    ·
      refine ⟨51094612583135789674163885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34063075055423859782775923 51094612583135789674163885)
      ·
        refine ⟨19160479718675921127811457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51094612583135789674163885 19160479718675921127811457)
        ·
          refine ⟨14370359789006940845858593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19160479718675921127811457 14370359789006940845858593)
          ·
            refine ⟨10777769841755205634393945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14370359789006940845858593 10777769841755205634393945)
            ·
              refine ⟨8083327381316404225795459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10777769841755205634393945 8083327381316404225795459)
              ·
                refine ⟨12124991071974606338693189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083327381316404225795459 12124991071974606338693189)
                ·
                  refine ⟨2273435825995238688504973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12124991071974606338693189 2273435825995238688504973)
                  ·
                    refine ⟨852538434748214508189365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273435825995238688504973 852538434748214508189365)
                    ·
                      rfl

theorem cell22_2490469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2490469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490469 prefixEnd_2490469 := by exact prefixLift 2490469
  have htrace : WordTrace (prefixWord ++ tailWord_2490469) baseStart_2490469 baseEnd_2490469 := by
    simpa [prefixWord, tailWord_2490469, baseEnd_2490469] using wordTrace_append hprefix tailTrace_2490469
  have hstable : (prefixWord ++ tailWord_2490469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490469).length < 2 ^ (prefixWord ++ tailWord_2490469).sum := by decide
  have hdescent : baseEnd_2490469 < baseStart_2490469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490471 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 4]
def baseStart_2490471 : Nat := 118140960795 + 2490471 * 2 ^ 59
def prefixEnd_2490471 : Nat := 4983230072969 + 3 ^ 40 * 2490471 * 2
def baseEnd_2490471 : Nat := 284179706463029056546453

theorem tailTrace_2490471 : CollatzResearch.WordTrace tailWord_2490471 prefixEnd_2490471 284179706463029056546453 := by
  unfold tailWord_2490471
  simp only [CollatzResearch.WordTrace]
  refine ⟨90834939760456380428975267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60556626506970920285983511 90834939760456380428975267)
  ·
    refine ⟨136252409640684570643462901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90834939760456380428975267 136252409640684570643462901)
    ·
      refine ⟨12773663403814178497824647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136252409640684570643462901 12773663403814178497824647)
      ·
        refine ⟨19160495105721267746736971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773663403814178497824647 19160495105721267746736971)
        ·
          refine ⟨28740742658581901620105457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160495105721267746736971 28740742658581901620105457)
          ·
            refine ⟨21555556993936426215079093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28740742658581901620105457 21555556993936426215079093)
            ·
              refine ⟨2020833468181539957663665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21555556993936426215079093 2020833468181539957663665)
              ·
                refine ⟨1515625101136154968247749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020833468181539957663665 1515625101136154968247749)
                ·
                  refine ⟨284179706463029056546453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515625101136154968247749 284179706463029056546453)
                  ·
                    rfl

theorem cell22_2490471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 4].length) (baseStart_2490471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490471 prefixEnd_2490471 := by exact prefixLift 2490471
  have htrace : WordTrace (prefixWord ++ tailWord_2490471) baseStart_2490471 baseEnd_2490471 := by
    simpa [prefixWord, tailWord_2490471, baseEnd_2490471] using wordTrace_append hprefix tailTrace_2490471
  have hstable : (prefixWord ++ tailWord_2490471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490471).length < 2 ^ (prefixWord ++ tailWord_2490471).sum := by decide
  have hdescent : baseEnd_2490471 < baseStart_2490471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490482 : List Nat := [3, 2, 1, 2, 2, 2, 1, 9]
def baseStart_2490482 : Nat := 118140960795 + 2490482 * 2 ^ 59
def prefixEnd_2490482 : Nat := 4983230072969 + 3 ^ 40 * 2490482 * 2
def baseEnd_2490482 : Nat := 94726987212654089734925

theorem tailTrace_2490482 : CollatzResearch.WordTrace tailWord_2490482 prefixEnd_2490482 94726987212654089734925 := by
  unfold tailWord_2490482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708835240854132326906425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60556893975611019538417133 22708835240854132326906425)
  ·
    refine ⟨17031626430640599245179819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22708835240854132326906425 17031626430640599245179819)
    ·
      refine ⟨25547439645960898867769729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17031626430640599245179819 25547439645960898867769729)
      ·
        refine ⟨19160579734470674150827297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25547439645960898867769729 19160579734470674150827297)
        ·
          refine ⟨14370434800853005613120473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19160579734470674150827297 14370434800853005613120473)
          ·
            refine ⟨10777826100639754209840355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14370434800853005613120473 10777826100639754209840355)
            ·
              refine ⟨16166739150959631314760533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10777826100639754209840355 16166739150959631314760533)
              ·
                refine ⟨94726987212654089734925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16166739150959631314760533 94726987212654089734925)
                ·
                  rfl

theorem cell22_2490482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_2490482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490482 prefixEnd_2490482 := by exact prefixLift 2490482
  have htrace : WordTrace (prefixWord ++ tailWord_2490482) baseStart_2490482 baseEnd_2490482 := by
    simpa [prefixWord, tailWord_2490482, baseEnd_2490482] using wordTrace_append hprefix tailTrace_2490482
  have hstable : (prefixWord ++ tailWord_2490482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490482).length < 2 ^ (prefixWord ++ tailWord_2490482).sum := by decide
  have hdescent : baseEnd_2490482 < baseStart_2490482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490516 : List Nat := [2, 4, 2, 3, 2, 9]
def baseStart_2490516 : Nat := 118140960795 + 2490516 * 2 ^ 59
def prefixEnd_2490516 : Nat := 4983230072969 + 3 ^ 40 * 2490516 * 2
def baseEnd_2490516 : Nat := 10525364491465704348941

theorem tailTrace_2490516 : CollatzResearch.WordTrace tailWord_2490516 prefixEnd_2490516 10525364491465704348941 := by
  unfold tailWord_2490516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45418290522646676557181701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60557720696862235409575601 45418290522646676557181701)
  ·
    refine ⟨8515929472996251854471569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45418290522646676557181701 8515929472996251854471569)
    ·
      refine ⟨6386947104747188890853677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8515929472996251854471569 6386947104747188890853677)
      ·
        refine ⟨2395105164280195834070129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6386947104747188890853677 2395105164280195834070129)
        ·
          refine ⟨1796328873210146875552597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395105164280195834070129 1796328873210146875552597)
          ·
            refine ⟨10525364491465704348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1796328873210146875552597 10525364491465704348941)
            ·
              rfl

theorem cell22_2490516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 9].length) (baseStart_2490516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490516 prefixEnd_2490516 := by exact prefixLift 2490516
  have htrace : WordTrace (prefixWord ++ tailWord_2490516) baseStart_2490516 baseEnd_2490516 := by
    simpa [prefixWord, tailWord_2490516, baseEnd_2490516] using wordTrace_append hprefix tailTrace_2490516
  have hstable : (prefixWord ++ tailWord_2490516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490516).length < 2 ^ (prefixWord ++ tailWord_2490516).sum := by decide
  have hdescent : baseEnd_2490516 < baseStart_2490516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_2490587 : Nat := 118140960795 + 2490587 * 2 ^ 59
def prefixEnd_2490587 : Nat := 4983230072969 + 3 ^ 40 * 2490587 * 2
def baseEnd_2490587 : Nat := 852578828559701533739003

theorem tailTrace_2490587 : CollatzResearch.WordTrace tailWord_2490587 prefixEnd_2490587 852578828559701533739003 := by
  unfold tailWord_2490587
  simp only [CollatzResearch.WordTrace]
  refine ⟨90839170628036132240198015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60559447085357421493465343 90839170628036132240198015)
  ·
    refine ⟨136258755942054198360297023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90839170628036132240198015 136258755942054198360297023)
    ·
      refine ⟨204388133913081297540445535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136258755942054198360297023 204388133913081297540445535)
      ·
        refine ⟨306582200869621946310668303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204388133913081297540445535 306582200869621946310668303)
        ·
          refine ⟨459873301304432919466002455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306582200869621946310668303 459873301304432919466002455)
          ·
            refine ⟨689809951956649379199003683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459873301304432919466002455 689809951956649379199003683)
            ·
              refine ⟨1034714927934974068798505525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689809951956649379199003683 1034714927934974068798505525)
              ·
                refine ⟨97004524493903818949859893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1034714927934974068798505525 97004524493903818949859893)
                ·
                  refine ⟨9094174171303483026549365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97004524493903818949859893 9094174171303483026549365)
                  ·
                    refine ⟨852578828559701533739003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9094174171303483026549365 852578828559701533739003)
                    ·
                      rfl

theorem cell22_2490587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_2490587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490587 prefixEnd_2490587 := by exact prefixLift 2490587
  have htrace : WordTrace (prefixWord ++ tailWord_2490587) baseStart_2490587 baseEnd_2490587 := by
    simpa [prefixWord, tailWord_2490587, baseEnd_2490587] using wordTrace_append hprefix tailTrace_2490587
  have hstable : (prefixWord ++ tailWord_2490587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490587).length < 2 ^ (prefixWord ++ tailWord_2490587).sum := by decide
  have hdescent : baseEnd_2490587 < baseStart_2490587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490655 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 2, 3]
def baseStart_2490655 : Nat := 118140960795 + 2490655 * 2 ^ 59
def prefixEnd_2490655 : Nat := 4983230072969 + 3 ^ 40 * 2490655 * 2
def baseEnd_2490655 : Nat := 852602106349372023038795

theorem tailTrace_2490655 : CollatzResearch.WordTrace tailWord_2490655 prefixEnd_2490655 852602106349372023038795 := by
  unfold tailWord_2490655
  simp only [CollatzResearch.WordTrace]
  refine ⟨90841650791789779853673419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60561100527859853235782279 90841650791789779853673419)
  ·
    refine ⟨136262476187684669780510129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90841650791789779853673419 136262476187684669780510129)
    ·
      refine ⟨102196857140763502335382597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136262476187684669780510129 102196857140763502335382597)
      ·
        refine ⟨19161910713893156687884237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102196857140763502335382597 19161910713893156687884237)
        ·
          refine ⟨7185716517709933757956589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19161910713893156687884237 7185716517709933757956589)
          ·
            refine ⟨2694643694141225159233721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7185716517709933757956589 2694643694141225159233721)
            ·
              refine ⟨2020982770605918869425291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694643694141225159233721 2020982770605918869425291)
              ·
                refine ⟨3031474155908878304137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020982770605918869425291 3031474155908878304137937)
                ·
                  refine ⟨2273605616931658728103453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031474155908878304137937 2273605616931658728103453)
                  ·
                    refine ⟨852602106349372023038795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273605616931658728103453 852602106349372023038795)
                    ·
                      rfl

theorem cell22_2490655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_2490655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490655 prefixEnd_2490655 := by exact prefixLift 2490655
  have htrace : WordTrace (prefixWord ++ tailWord_2490655) baseStart_2490655 baseEnd_2490655 := by
    simpa [prefixWord, tailWord_2490655, baseEnd_2490655] using wordTrace_append hprefix tailTrace_2490655
  have hstable : (prefixWord ++ tailWord_2490655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490655).length < 2 ^ (prefixWord ++ tailWord_2490655).sum := by decide
  have hdescent : baseEnd_2490655 < baseStart_2490655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490670 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2490670 : Nat := 118140960795 + 2490670 * 2 ^ 59
def prefixEnd_2490670 : Nat := 4983230072969 + 3 ^ 40 * 2490670 * 2
def baseEnd_2490670 : Nat := 852607241155916983913749

theorem tailTrace_2490670 : CollatzResearch.WordTrace tailWord_2490670 prefixEnd_2490670 852607241155916983913749 := by
  unfold tailWord_2490670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355274735841929676933683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60561465257823624943646309 11355274735841929676933683)
  ·
    refine ⟨17032912103762894515400525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11355274735841929676933683 17032912103762894515400525)
    ·
      refine ⟨6387342038911085443275197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17032912103762894515400525 6387342038911085443275197)
      ·
        refine ⟨2395253264591657041228199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6387342038911085443275197 2395253264591657041228199)
        ·
          refine ⟨3592879896887485561842299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2395253264591657041228199 3592879896887485561842299)
          ·
            refine ⟨5389319845331228342763449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592879896887485561842299 5389319845331228342763449)
            ·
              refine ⟨4041989883998421257072587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5389319845331228342763449 4041989883998421257072587)
              ·
                refine ⟨6062984825997631885608881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041989883998421257072587 6062984825997631885608881)
                ·
                  refine ⟨4547238619498223914206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062984825997631885608881 4547238619498223914206661)
                  ·
                    refine ⟨852607241155916983913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547238619498223914206661 852607241155916983913749)
                    ·
                      rfl

theorem cell22_2490670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2490670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490670 prefixEnd_2490670 := by exact prefixLift 2490670
  have htrace : WordTrace (prefixWord ++ tailWord_2490670) baseStart_2490670 baseEnd_2490670 := by
    simpa [prefixWord, tailWord_2490670, baseEnd_2490670] using wordTrace_append hprefix tailTrace_2490670
  have hstable : (prefixWord ++ tailWord_2490670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490670).length < 2 ^ (prefixWord ++ tailWord_2490670).sum := by decide
  have hdescent : baseEnd_2490670 < baseStart_2490670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490786 : List Nat := [3, 3, 1, 2, 1, 1, 3, 8]
def baseStart_2490786 : Nat := 118140960795 + 2490786 * 2 ^ 59
def prefixEnd_2490786 : Nat := 4983230072969 + 3 ^ 40 * 2490786 * 2
def baseEnd_2490786 : Nat := 94738550036281260890377

theorem tailTrace_2490786 : CollatzResearch.WordTrace tailWord_2490786 prefixEnd_2490786 94738550036281260890377 := by
  unfold tailWord_2490786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22711607188578797306673053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60564285836210126151128141 22711607188578797306673053)
  ·
    refine ⟨8516852695717048990002395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22711607188578797306673053 8516852695717048990002395)
    ·
      refine ⟨12775279043575573485003593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516852695717048990002395 12775279043575573485003593)
      ·
        refine ⟨9581459282681680113752695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12775279043575573485003593 9581459282681680113752695)
        ·
          refine ⟨14372188924022520170629043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9581459282681680113752695 14372188924022520170629043)
          ·
            refine ⟨21558283386033780255943565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14372188924022520170629043 21558283386033780255943565)
            ·
              refine ⟨8084356269762667595978837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21558283386033780255943565 8084356269762667595978837)
              ·
                refine ⟨94738550036281260890377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8084356269762667595978837 94738550036281260890377)
                ·
                  rfl

theorem cell22_2490786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_2490786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490786 prefixEnd_2490786 := by exact prefixLift 2490786
  have htrace : WordTrace (prefixWord ++ tailWord_2490786) baseStart_2490786 baseEnd_2490786 := by
    simpa [prefixWord, tailWord_2490786, baseEnd_2490786] using wordTrace_append hprefix tailTrace_2490786
  have hstable : (prefixWord ++ tailWord_2490786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490786).length < 2 ^ (prefixWord ++ tailWord_2490786).sum := by decide
  have hdescent : baseEnd_2490786 < baseStart_2490786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490792 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_2490792 : Nat := 118140960795 + 2490792 * 2 ^ 59
def prefixEnd_2490792 : Nat := 4983230072969 + 3 ^ 40 * 2490792 * 2
def baseEnd_2490792 : Nat := 284216334749716444121125

theorem tailTrace_2490792 : CollatzResearch.WordTrace tailWord_2490792 prefixEnd_2490792 284216334749716444121125 := by
  unfold tailWord_2490792
  simp only [CollatzResearch.WordTrace]
  refine ⟨45423323796146726125705315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60564431728195634834273753 45423323796146726125705315)
  ·
    refine ⟨68134985694220089188557973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45423323796146726125705315 68134985694220089188557973)
    ·
      refine ⟨3193827454416566680713655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68134985694220089188557973 3193827454416566680713655)
      ·
        refine ⟨4790741181624850021070483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193827454416566680713655 4790741181624850021070483)
        ·
          refine ⟨7186111772437275031605725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790741181624850021070483 7186111772437275031605725)
          ·
            refine ⟨2694791914663978136852147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7186111772437275031605725 2694791914663978136852147)
            ·
              refine ⟨4042187871995967205278221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694791914663978136852147 4042187871995967205278221)
              ·
                refine ⟨1515820451998487701979333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4042187871995967205278221 1515820451998487701979333)
                ·
                  refine ⟨284216334749716444121125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515820451998487701979333 284216334749716444121125)
                  ·
                    rfl

theorem cell22_2490792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_2490792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490792 prefixEnd_2490792 := by exact prefixLift 2490792
  have htrace : WordTrace (prefixWord ++ tailWord_2490792) baseStart_2490792 baseEnd_2490792 := by
    simpa [prefixWord, tailWord_2490792, baseEnd_2490792] using wordTrace_append hprefix tailTrace_2490792
  have hstable : (prefixWord ++ tailWord_2490792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490792).length < 2 ^ (prefixWord ++ tailWord_2490792).sum := by decide
  have hdescent : baseEnd_2490792 < baseStart_2490792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490799 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2490799 : Nat := 118140960795 + 2490799 * 2 ^ 59
def prefixEnd_2490799 : Nat := 4983230072969 + 3 ^ 40 * 2490799 * 2
def baseEnd_2490799 : Nat := 852651400492203647438353

theorem tailTrace_2490799 : CollatzResearch.WordTrace tailWord_2490799 prefixEnd_2490799 852651400492203647438353 := by
  unfold tailWord_2490799
  simp only [CollatzResearch.WordTrace]
  refine ⟨90846902903268092446915451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60564601935512061631276967 90846902903268092446915451)
  ·
    refine ⟨136270354354902138670373177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90846902903268092446915451 136270354354902138670373177)
    ·
      refine ⟨102202765766176604002779883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136270354354902138670373177 102202765766176604002779883)
      ·
        refine ⟨153304148649264906004169825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102202765766176604002779883 153304148649264906004169825)
        ·
          refine ⟨114978111486948679503127369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153304148649264906004169825 114978111486948679503127369)
          ·
            refine ⟨86233583615211509627345527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114978111486948679503127369 86233583615211509627345527)
            ·
              refine ⟨129350375422817264441018291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86233583615211509627345527 129350375422817264441018291)
              ·
                refine ⟨194025563134225896661527437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129350375422817264441018291 194025563134225896661527437)
                ·
                  refine ⟨72759586175334711248072789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194025563134225896661527437 72759586175334711248072789)
                  ·
                    refine ⟨852651400492203647438353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72759586175334711248072789 852651400492203647438353)
                    ·
                      rfl

theorem cell22_2490799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2490799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490799 prefixEnd_2490799 := by exact prefixLift 2490799
  have htrace : WordTrace (prefixWord ++ tailWord_2490799) baseStart_2490799 baseEnd_2490799 := by
    simpa [prefixWord, tailWord_2490799, baseEnd_2490799] using wordTrace_append hprefix tailTrace_2490799
  have hstable : (prefixWord ++ tailWord_2490799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490799).length < 2 ^ (prefixWord ++ tailWord_2490799).sum := by decide
  have hdescent : baseEnd_2490799 < baseStart_2490799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490869 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2490869 : Nat := 118140960795 + 2490869 * 2 ^ 59
def prefixEnd_2490869 : Nat := 4983230072969 + 3 ^ 40 * 2490869 * 2
def baseEnd_2490869 : Nat := 852675362922746798188139

theorem tailTrace_2490869 : CollatzResearch.WordTrace tailWord_2490869 prefixEnd_2490869 852675362922746798188139 := by
  unfold tailWord_2490869
  simp only [CollatzResearch.WordTrace]
  refine ⟨90849456013014494401963661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60566304008676329601309107 90849456013014494401963661)
  ·
    refine ⟨34068546004880435400736373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90849456013014494401963661 34068546004880435400736373)
    ·
      refine ⟨3193926187957540818819035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34068546004880435400736373 3193926187957540818819035)
      ·
        refine ⟨4790889281936311228228553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193926187957540818819035 4790889281936311228228553)
        ·
          refine ⟨3593166961452233421171415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790889281936311228228553 3593166961452233421171415)
          ·
            refine ⟨5389750442178350131757123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593166961452233421171415 5389750442178350131757123)
            ·
              refine ⟨8084625663267525197635685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389750442178350131757123 8084625663267525197635685)
              ·
                refine ⟨1515867311862660974556691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8084625663267525197635685 1515867311862660974556691)
                ·
                  refine ⟨2273800967793991461835037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515867311862660974556691 2273800967793991461835037)
                  ·
                    refine ⟨852675362922746798188139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273800967793991461835037 852675362922746798188139)
                    ·
                      rfl

theorem cell22_2490869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2490869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490869 prefixEnd_2490869 := by exact prefixLift 2490869
  have htrace : WordTrace (prefixWord ++ tailWord_2490869) baseStart_2490869 baseEnd_2490869 := by
    simpa [prefixWord, tailWord_2490869, baseEnd_2490869] using wordTrace_append hprefix tailTrace_2490869
  have hstable : (prefixWord ++ tailWord_2490869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490869).length < 2 ^ (prefixWord ++ tailWord_2490869).sum := by decide
  have hdescent : baseEnd_2490869 < baseStart_2490869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490876 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_2490876 : Nat := 118140960795 + 2490876 * 2 ^ 59
def prefixEnd_2490876 : Nat := 4983230072969 + 3 ^ 40 * 2490876 * 2
def baseEnd_2490876 : Nat := 284225919721933704421039

theorem tailTrace_2490876 : CollatzResearch.WordTrace tailWord_2490876 prefixEnd_2490876 284225919721933704421039 := by
  unfold tailWord_2490876
  simp only [CollatzResearch.WordTrace]
  refine ⟨45424855661994567298734241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60566474215992756398312321 45424855661994567298734241)
  ·
    refine ⟨34068641746495925474050681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45424855661994567298734241 34068641746495925474050681)
    ·
      refine ⟨25551481309871944105538011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34068641746495925474050681 25551481309871944105538011)
      ·
        refine ⟨38327221964807916158307017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25551481309871944105538011 38327221964807916158307017)
        ·
          refine ⟨28745416473605937118730263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38327221964807916158307017 28745416473605937118730263)
          ·
            refine ⟨43118124710408905678095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28745416473605937118730263 43118124710408905678095395)
            ·
              refine ⟨64677187065613358517143093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43118124710408905678095395 64677187065613358517143093)
              ·
                refine ⟨6063486287401252360982165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64677187065613358517143093 6063486287401252360982165)
                ·
                  refine ⟨284225919721933704421039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6063486287401252360982165 284225919721933704421039)
                  ·
                    rfl

theorem cell22_2490876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_2490876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490876 prefixEnd_2490876 := by exact prefixLift 2490876
  have htrace : WordTrace (prefixWord ++ tailWord_2490876) baseStart_2490876 baseEnd_2490876 := by
    simpa [prefixWord, tailWord_2490876, baseEnd_2490876] using wordTrace_append hprefix tailTrace_2490876
  have hstable : (prefixWord ++ tailWord_2490876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490876).length < 2 ^ (prefixWord ++ tailWord_2490876).sum := by decide
  have hdescent : baseEnd_2490876 < baseStart_2490876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490908 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2490908 : Nat := 118140960795 + 2490908 * 2 ^ 59
def prefixEnd_2490908 : Nat := 4983230072969 + 3 ^ 40 * 2490908 * 2
def baseEnd_2490908 : Nat := 852688713419763696463019

theorem tailTrace_2490908 : CollatzResearch.WordTrace tailWord_2490908 prefixEnd_2490908 852688713419763696463019 := by
  unfold tailWord_2490908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45425439229936602031316689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60567252306582136041755585 45425439229936602031316689)
  ·
    refine ⟨34069079422452451523487517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45425439229936602031316689 34069079422452451523487517)
    ·
      refine ⟨12775904783419669321307819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34069079422452451523487517 12775904783419669321307819)
      ·
        refine ⟨19163857175129503981961729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12775904783419669321307819 19163857175129503981961729)
        ·
          refine ⟨14372892881347127986471297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19163857175129503981961729 14372892881347127986471297)
          ·
            refine ⟨10779669661010345989853473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14372892881347127986471297 10779669661010345989853473)
            ·
              refine ⟨8084752245757759492390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10779669661010345989853473 8084752245757759492390105)
              ·
                refine ⟨6063564184318319619292579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8084752245757759492390105 6063564184318319619292579)
                ·
                  refine ⟨9095346276477479428938869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063564184318319619292579 9095346276477479428938869)
                  ·
                    refine ⟨852688713419763696463019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9095346276477479428938869 852688713419763696463019)
                    ·
                      rfl

theorem cell22_2490908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2490908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490908 prefixEnd_2490908 := by exact prefixLift 2490908
  have htrace : WordTrace (prefixWord ++ tailWord_2490908) baseStart_2490908 baseEnd_2490908 := by
    simpa [prefixWord, tailWord_2490908, baseEnd_2490908] using wordTrace_append hprefix tailTrace_2490908
  have hstable : (prefixWord ++ tailWord_2490908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490908).length < 2 ^ (prefixWord ++ tailWord_2490908).sum := by decide
  have hdescent : baseEnd_2490908 < baseStart_2490908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490983 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 5]
def baseStart_2490983 : Nat := 118140960795 + 2490983 * 2 ^ 59
def prefixEnd_2490983 : Nat := 4983230072969 + 3 ^ 40 * 2490983 * 2
def baseEnd_2490983 : Nat := 284238129150829500279263

theorem tailTrace_2490983 : CollatzResearch.WordTrace tailWord_2490983 prefixEnd_2490983 284238129150829500279263 := by
  unfold tailWord_2490983
  simp only [CollatzResearch.WordTrace]
  refine ⟨90853613934601491871613603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60569075956400994581075735 90853613934601491871613603)
  ·
    refine ⟨136280420901902237807420405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90853613934601491871613603 136280420901902237807420405)
    ·
      refine ⟨12776289459553334794445663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136280420901902237807420405 12776289459553334794445663)
      ·
        refine ⟨19164434189330002191668495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12776289459553334794445663 19164434189330002191668495)
        ·
          refine ⟨28746651283995003287502743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19164434189330002191668495 28746651283995003287502743)
          ·
            refine ⟨43119976925992504931254115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28746651283995003287502743 43119976925992504931254115)
            ·
              refine ⟨64679965388988757396881173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43119976925992504931254115 64679965388988757396881173)
              ·
                refine ⟨3031873377608848002978805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64679965388988757396881173 3031873377608848002978805)
                ·
                  refine ⟨284238129150829500279263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031873377608848002978805 284238129150829500279263)
                  ·
                    rfl

theorem cell22_2490983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].length) (baseStart_2490983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2490983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2490983 prefixEnd_2490983 := by exact prefixLift 2490983
  have htrace : WordTrace (prefixWord ++ tailWord_2490983) baseStart_2490983 baseEnd_2490983 := by
    simpa [prefixWord, tailWord_2490983, baseEnd_2490983] using wordTrace_append hprefix tailTrace_2490983
  have hstable : (prefixWord ++ tailWord_2490983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490983).length < 2 ^ (prefixWord ++ tailWord_2490983).sum := by decide
  have hdescent : baseEnd_2490983 < baseStart_2490983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491058 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2491058 : Nat := 118140960795 + 2491058 * 2 ^ 59
def prefixEnd_2491058 : Nat := 4983230072969 + 3 ^ 40 * 2491058 * 2
def baseEnd_2491058 : Nat := 852740061485213305212559

theorem tailTrace_2491058 : CollatzResearch.WordTrace tailWord_2491058 prefixEnd_2491058 852740061485213305212559 := by
  unfold tailWord_2491058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22714087352332444920148457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60570899606219853120395885 22714087352332444920148457)
  ·
    refine ⟨17035565514249333690111343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22714087352332444920148457 17035565514249333690111343)
    ·
      refine ⟨25553348271374000535167015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17035565514249333690111343 25553348271374000535167015)
      ·
        refine ⟨38330022407061000802750523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25553348271374000535167015 38330022407061000802750523)
        ·
          refine ⟨57495033610591501204125785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38330022407061000802750523 57495033610591501204125785)
          ·
            refine ⟨43121275207943625903094339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57495033610591501204125785 43121275207943625903094339)
            ·
              refine ⟨64681912811915438854641509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43121275207943625903094339 64681912811915438854641509)
              ·
                refine ⟨12127858652234144785245283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64681912811915438854641509 12127858652234144785245283)
                ·
                  refine ⟨18191787978351217177867925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12127858652234144785245283 18191787978351217177867925)
                  ·
                    refine ⟨852740061485213305212559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18191787978351217177867925 852740061485213305212559)
                    ·
                      rfl

theorem cell22_2491058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2491058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491058 prefixEnd_2491058 := by exact prefixLift 2491058
  have htrace : WordTrace (prefixWord ++ tailWord_2491058) baseStart_2491058 baseEnd_2491058 := by
    simpa [prefixWord, tailWord_2491058, baseEnd_2491058] using wordTrace_append hprefix tailTrace_2491058
  have hstable : (prefixWord ++ tailWord_2491058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491058).length < 2 ^ (prefixWord ++ tailWord_2491058).sum := by decide
  have hdescent : baseEnd_2491058 < baseStart_2491058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491090 : List Nat := [3, 2, 2, 2, 3, 1, 9]
def baseStart_2491090 : Nat := 118140960795 + 2491090 * 2 ^ 59
def prefixEnd_2491090 : Nat := 4983230072969 + 3 ^ 40 * 2491090 * 2
def baseEnd_2491090 : Nat := 31583370953302810681943

theorem tailTrace_2491090 : CollatzResearch.WordTrace tailWord_2491090 prefixEnd_2491090 31583370953302810681943 := by
  unfold tailWord_2491090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22714379136303462286439681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60571677696809232763839149 22714379136303462286439681)
  ·
    refine ⟨17035784352227596714829761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22714379136303462286439681 17035784352227596714829761)
    ·
      refine ⟨12776838264170697536122321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17035784352227596714829761 12776838264170697536122321)
      ·
        refine ⟨9582628698128023152091741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12776838264170697536122321 9582628698128023152091741)
        ·
          refine ⟨3593485761798008682034403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9582628698128023152091741 3593485761798008682034403)
          ·
            refine ⟨5390228642697013023051605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593485761798008682034403 5390228642697013023051605)
            ·
              refine ⟨31583370953302810681943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5390228642697013023051605 31583370953302810681943)
              ·
                rfl

theorem cell22_2491090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 9].length) (baseStart_2491090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491090 prefixEnd_2491090 := by exact prefixLift 2491090
  have htrace : WordTrace (prefixWord ++ tailWord_2491090) baseStart_2491090 baseEnd_2491090 := by
    simpa [prefixWord, tailWord_2491090, baseEnd_2491090] using wordTrace_append hprefix tailTrace_2491090
  have hstable : (prefixWord ++ tailWord_2491090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491090).length < 2 ^ (prefixWord ++ tailWord_2491090).sum := by decide
  have hdescent : baseEnd_2491090 < baseStart_2491090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491122 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_2491122 : Nat := 118140960795 + 2491122 * 2 ^ 59
def prefixEnd_2491122 : Nat := 4983230072969 + 3 ^ 40 * 2491122 * 2
def baseEnd_2491122 : Nat := 852761969993138471612363

theorem tailTrace_2491122 : CollatzResearch.WordTrace tailWord_2491122 prefixEnd_2491122 852761969993138471612363 := by
  unfold tailWord_2491122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22714670920274479652730905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60572455787398612407282413 22714670920274479652730905)
  ·
    refine ⟨17036003190205859739548179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22714670920274479652730905 17036003190205859739548179)
    ·
      refine ⟨25554004785308789609322269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17036003190205859739548179 25554004785308789609322269)
      ·
        refine ⟨9582751794490796103495851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25554004785308789609322269 9582751794490796103495851)
        ·
          refine ⟨14374127691736194155243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582751794490796103495851 14374127691736194155243777)
          ·
            refine ⟨10780595768802145616432833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14374127691736194155243777 10780595768802145616432833)
            ·
              refine ⟨8085446826601609212324625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10780595768802145616432833 8085446826601609212324625)
              ·
                refine ⟨6064085119951206909243469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085446826601609212324625 6064085119951206909243469)
                ·
                  refine ⟨2274031919981702590966301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6064085119951206909243469 2274031919981702590966301)
                  ·
                    refine ⟨852761969993138471612363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274031919981702590966301 852761969993138471612363)
                    ·
                      rfl

theorem cell22_2491122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_2491122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491122 prefixEnd_2491122 := by exact prefixLift 2491122
  have htrace : WordTrace (prefixWord ++ tailWord_2491122) baseStart_2491122 baseEnd_2491122 := by
    simpa [prefixWord, tailWord_2491122, baseEnd_2491122] using wordTrace_append hprefix tailTrace_2491122
  have hstable : (prefixWord ++ tailWord_2491122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491122).length < 2 ^ (prefixWord ++ tailWord_2491122).sum := by decide
  have hdescent : baseEnd_2491122 < baseStart_2491122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491124 : List Nat := [2, 6, 1, 1, 2, 1, 1, 8]
def baseStart_2491124 : Nat := 118140960795 + 2491124 * 2 ^ 59
def prefixEnd_2491124 : Nat := 4983230072969 + 3 ^ 40 * 2491124 * 2
def baseEnd_2491124 : Nat := 94751406070445681451373

theorem tailTrace_2491124 : CollatzResearch.WordTrace tailWord_2491124 prefixEnd_2491124 94751406070445681451373 := by
  unfold tailWord_2491124
  simp only [CollatzResearch.WordTrace]
  refine ⟨45429378313545336476248213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60572504418060448634997617 45429378313545336476248213)
  ·
    refine ⟨2129502108447437647324135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45429378313545336476248213 2129502108447437647324135)
    ·
      refine ⟨3194253162671156470986203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2129502108447437647324135 3194253162671156470986203)
      ·
        refine ⟨4791379744006734706479305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194253162671156470986203 4791379744006734706479305)
        ·
          refine ⟨3593534808005051029859479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4791379744006734706479305 3593534808005051029859479)
          ·
            refine ⟨5390302212007576544789219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593534808005051029859479 5390302212007576544789219)
            ·
              refine ⟨8085453318011364817183829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390302212007576544789219 8085453318011364817183829)
              ·
                refine ⟨94751406070445681451373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8085453318011364817183829 94751406070445681451373)
                ·
                  rfl

theorem cell22_2491124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_2491124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491124 prefixEnd_2491124 := by exact prefixLift 2491124
  have htrace : WordTrace (prefixWord ++ tailWord_2491124) baseStart_2491124 baseEnd_2491124 := by
    simpa [prefixWord, tailWord_2491124, baseEnd_2491124] using wordTrace_append hprefix tailTrace_2491124
  have hstable : (prefixWord ++ tailWord_2491124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491124).length < 2 ^ (prefixWord ++ tailWord_2491124).sum := by decide
  have hdescent : baseEnd_2491124 < baseStart_2491124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491199 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 1, 4]
def baseStart_2491199 : Nat := 118140960795 + 2491199 * 2 ^ 59
def prefixEnd_2491199 : Nat := 4983230072969 + 3 ^ 40 * 2491199 * 2
def baseEnd_2491199 : Nat := 852788328666735937437127

theorem tailTrace_2491199 : CollatzResearch.WordTrace tailWord_2491199 prefixEnd_2491199 852788328666735937437127 := by
  unfold tailWord_2491199
  simp only [CollatzResearch.WordTrace]
  refine ⟨90861492101818960761476651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60574328067879307174317767 90861492101818960761476651)
  ·
    refine ⟨136292238152728441142214977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90861492101818960761476651 136292238152728441142214977)
    ·
      refine ⟨102219178614546330856661233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136292238152728441142214977 102219178614546330856661233)
      ·
        refine ⟨76664383960909748142495925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102219178614546330856661233 76664383960909748142495925)
        ·
          refine ⟨7187285996335288888358993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76664383960909748142495925 7187285996335288888358993)
          ·
            refine ⟨5390464497251466666269245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7187285996335288888358993 5390464497251466666269245)
            ·
              refine ⟨2021424186469299999850967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5390464497251466666269245 2021424186469299999850967)
              ·
                refine ⟨3032136279703949999776451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021424186469299999850967 3032136279703949999776451)
                ·
                  refine ⟨4548204419555924999664677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032136279703949999776451 4548204419555924999664677)
                  ·
                    refine ⟨852788328666735937437127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4548204419555924999664677 852788328666735937437127)
                    ·
                      rfl

theorem cell22_2491199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_2491199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491199 prefixEnd_2491199 := by exact prefixLift 2491199
  have htrace : WordTrace (prefixWord ++ tailWord_2491199) baseStart_2491199 baseEnd_2491199 := by
    simpa [prefixWord, tailWord_2491199, baseEnd_2491199] using wordTrace_append hprefix tailTrace_2491199
  have hstable : (prefixWord ++ tailWord_2491199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491199).length < 2 ^ (prefixWord ++ tailWord_2491199).sum := by decide
  have hdescent : baseEnd_2491199 < baseStart_2491199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491210 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2491210 : Nat := 118140960795 + 2491210 * 2 ^ 59
def prefixEnd_2491210 : Nat := 4983230072969 + 3 ^ 40 * 2491210 * 2
def baseEnd_2491210 : Nat := 852792094191535575412093

theorem tailTrace_2491210 : CollatzResearch.WordTrace tailWord_2491210 prefixEnd_2491210 852792094191535575412093 := by
  unfold tailWord_2491210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22715473326194777410031771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60574595536519406426751389 22715473326194777410031771)
  ·
    refine ⟨34073209989292166115047657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22715473326194777410031771 34073209989292166115047657)
    ·
      refine ⟨25554907491969124586285743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34073209989292166115047657 25554907491969124586285743)
      ·
        refine ⟨38332361237953686879428615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25554907491969124586285743 38332361237953686879428615)
        ·
          refine ⟨57498541856930530319142923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38332361237953686879428615 57498541856930530319142923)
          ·
            refine ⟨86247812785395795478714385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57498541856930530319142923 86247812785395795478714385)
            ·
              refine ⟨64685859589046846609035789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86247812785395795478714385 64685859589046846609035789)
              ·
                refine ⟨24257197345892567478388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64685859589046846609035789 24257197345892567478388421)
                ·
                  refine ⟨4548224502354856402197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24257197345892567478388421 4548224502354856402197829)
                  ·
                    refine ⟨852792094191535575412093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4548224502354856402197829 852792094191535575412093)
                    ·
                      rfl

theorem cell22_2491210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2491210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491210 prefixEnd_2491210 := by exact prefixLift 2491210
  have htrace : WordTrace (prefixWord ++ tailWord_2491210) baseStart_2491210 baseEnd_2491210 := by
    simpa [prefixWord, tailWord_2491210, baseEnd_2491210] using wordTrace_append hprefix tailTrace_2491210
  have hstable : (prefixWord ++ tailWord_2491210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491210).length < 2 ^ (prefixWord ++ tailWord_2491210).sum := by decide
  have hdescent : baseEnd_2491210 < baseStart_2491210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491225 : List Nat := [1, 2, 1, 2, 2, 4, 3, 7]
def baseStart_2491225 : Nat := 118140960795 + 2491225 * 2 ^ 59
def prefixEnd_2491225 : Nat := 4983230072969 + 3 ^ 40 * 2491225 * 2
def baseEnd_2491225 : Nat := 94755247666453392920783

theorem tailTrace_2491225 : CollatzResearch.WordTrace tailWord_2491225 prefixEnd_2491225 94755247666453392920783 := by
  unfold tailWord_2491225
  simp only [CollatzResearch.WordTrace]
  refine ⟨90862440399724767201923129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60574960266483178134615419 90862440399724767201923129)
  ·
    refine ⟨68146830299793575401442347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90862440399724767201923129 68146830299793575401442347)
    ·
      refine ⟨102220245449690363102163521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68146830299793575401442347 102220245449690363102163521)
      ·
        refine ⟨76665184087267772326622641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102220245449690363102163521 76665184087267772326622641)
        ·
          refine ⟨57498888065450829244966981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76665184087267772326622641 57498888065450829244966981)
          ·
            refine ⟨10781041512272030483431309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57498888065450829244966981 10781041512272030483431309)
            ·
              refine ⟨4042890567102011431286741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10781041512272030483431309 4042890567102011431286741)
              ·
                refine ⟨94755247666453392920783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4042890567102011431286741 94755247666453392920783)
                ·
                  rfl

theorem cell22_2491225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 7].length) (baseStart_2491225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491225 prefixEnd_2491225 := by exact prefixLift 2491225
  have htrace : WordTrace (prefixWord ++ tailWord_2491225) baseStart_2491225 baseEnd_2491225 := by
    simpa [prefixWord, tailWord_2491225, baseEnd_2491225] using wordTrace_append hprefix tailTrace_2491225
  have hstable : (prefixWord ++ tailWord_2491225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491225).length < 2 ^ (prefixWord ++ tailWord_2491225).sum := by decide
  have hdescent : baseEnd_2491225 < baseStart_2491225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491274 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2491274 : Nat := 118140960795 + 2491274 * 2 ^ 59
def prefixEnd_2491274 : Nat := 4983230072969 + 3 ^ 40 * 2491274 * 2
def baseEnd_2491274 : Nat := 852814002699460741811897

theorem tailTrace_2491274 : CollatzResearch.WordTrace tailWord_2491274 prefixEnd_2491274 852814002699460741811897 := by
  unfold tailWord_2491274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716056894136812142614219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60576151717698165713637917 22716056894136812142614219)
  ·
    refine ⟨34074085341205218213921329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716056894136812142614219 34074085341205218213921329)
    ·
      refine ⟨25555564005903913660440997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34074085341205218213921329 25555564005903913660440997)
      ·
        refine ⟨4791668251106983811332687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25555564005903913660440997 4791668251106983811332687)
        ·
          refine ⟨7187502376660475716999031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791668251106983811332687 7187502376660475716999031)
          ·
            refine ⟨10781253564990713575498547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187502376660475716999031 10781253564990713575498547)
            ·
              refine ⟨16171880347486070363247821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781253564990713575498547 16171880347486070363247821)
              ·
                refine ⟨6064455130307276386217933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16171880347486070363247821 6064455130307276386217933)
                ·
                  refine ⟨2274170673865228644831725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6064455130307276386217933 2274170673865228644831725)
                  ·
                    refine ⟨852814002699460741811897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274170673865228644831725 852814002699460741811897)
                    ·
                      rfl

theorem cell22_2491274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2491274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491274 prefixEnd_2491274 := by exact prefixLift 2491274
  have htrace : WordTrace (prefixWord ++ tailWord_2491274) baseStart_2491274 baseEnd_2491274 := by
    simpa [prefixWord, tailWord_2491274, baseEnd_2491274] using wordTrace_append hprefix tailTrace_2491274
  have hstable : (prefixWord ++ tailWord_2491274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491274).length < 2 ^ (prefixWord ++ tailWord_2491274).sum := by decide
  have hdescent : baseEnd_2491274 < baseStart_2491274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491501 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2491501 : Nat := 118140960795 + 2491501 * 2 ^ 59
def prefixEnd_2491501 : Nat := 4983230072969 + 3 ^ 40 * 2491501 * 2
def baseEnd_2491501 : Nat := 284297236479502605462067

theorem tailTrace_2491501 : CollatzResearch.WordTrace tailWord_2491501 prefixEnd_2491501 284297236479502605462067 := by
  unfold tailWord_2491501
  simp only [CollatzResearch.WordTrace]
  refine ⟨90872506946724866338970357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60581671297816577559313571 90872506946724866338970357)
  ·
    refine ⟨8519297526255456219278471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90872506946724866338970357 8519297526255456219278471)
    ·
      refine ⟨12778946289383184328917707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519297526255456219278471 12778946289383184328917707)
      ·
        refine ⟨19168419434074776493376561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12778946289383184328917707 19168419434074776493376561)
        ·
          refine ⟨14376314575556082370032421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19168419434074776493376561 14376314575556082370032421)
          ·
            refine ⟨2695558982916765444381079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14376314575556082370032421 2695558982916765444381079)
            ·
              refine ⟨4043338474375148166571619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695558982916765444381079 4043338474375148166571619)
              ·
                refine ⟨6065007711562722249857429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043338474375148166571619 6065007711562722249857429)
                ·
                  refine ⟨284297236479502605462067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065007711562722249857429 284297236479502605462067)
                  ·
                    rfl

theorem cell22_2491501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2491501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491501 prefixEnd_2491501 := by exact prefixLift 2491501
  have htrace : WordTrace (prefixWord ++ tailWord_2491501) baseStart_2491501 baseEnd_2491501 := by
    simpa [prefixWord, tailWord_2491501, baseEnd_2491501] using wordTrace_append hprefix tailTrace_2491501
  have hstable : (prefixWord ++ tailWord_2491501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491501).length < 2 ^ (prefixWord ++ tailWord_2491501).sum := by decide
  have hdescent : baseEnd_2491501 < baseStart_2491501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491512 : List Nat := [2, 1, 2, 1, 1, 1, 5, 9]
def baseStart_2491512 : Nat := 118140960795 + 2491512 * 2 ^ 59
def prefixEnd_2491512 : Nat := 4983230072969 + 3 ^ 40 * 2491512 * 2
def baseEnd_2491512 : Nat := 94766163884811939373463

theorem tailTrace_2491512 : CollatzResearch.WordTrace tailWord_2491512 prefixEnd_2491512 94766163884811939373463 := by
  unfold tailWord_2491512
  simp only [CollatzResearch.WordTrace]
  refine ⟨45436454074842507608810395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60581938766456676811747193 45436454074842507608810395)
  ·
    refine ⟨68154681112263761413215593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45436454074842507608810395 68154681112263761413215593)
    ·
      refine ⟨51116010834197821059911695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68154681112263761413215593 51116010834197821059911695)
      ·
        refine ⟨76674016251296731589867543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51116010834197821059911695 76674016251296731589867543)
        ·
          refine ⟨115011024376945097384801315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76674016251296731589867543 115011024376945097384801315)
          ·
            refine ⟨172516536565417646077201973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115011024376945097384801315 172516536565417646077201973)
            ·
              refine ⟨16173425303007904319737685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172516536565417646077201973 16173425303007904319737685)
              ·
                refine ⟨94766163884811939373463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16173425303007904319737685 94766163884811939373463)
                ·
                  rfl

theorem cell22_2491512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_2491512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491512 prefixEnd_2491512 := by exact prefixLift 2491512
  have htrace : WordTrace (prefixWord ++ tailWord_2491512) baseStart_2491512 baseEnd_2491512 := by
    simpa [prefixWord, tailWord_2491512, baseEnd_2491512] using wordTrace_append hprefix tailTrace_2491512
  have hstable : (prefixWord ++ tailWord_2491512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491512).length < 2 ^ (prefixWord ++ tailWord_2491512).sum := by decide
  have hdescent : baseEnd_2491512 < baseStart_2491512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491516 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2491516 : Nat := 118140960795 + 2491516 * 2 ^ 59
def prefixEnd_2491516 : Nat := 4983230072969 + 3 ^ 40 * 2491516 * 2
def baseEnd_2491516 : Nat := 852896844245052777261155

theorem tailTrace_2491516 : CollatzResearch.WordTrace tailWord_2491516 prefixEnd_2491516 852896844245052777261155 := by
  unfold tailWord_2491516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45436527020835261950383201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60582036027780349267177601 45436527020835261950383201)
  ·
    refine ⟨34077395265626446462787401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45436527020835261950383201 34077395265626446462787401)
    ·
      refine ⟨25558046449219834847090551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34077395265626446462787401 25558046449219834847090551)
      ·
        refine ⟨38337069673829752270635827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25558046449219834847090551 38337069673829752270635827)
        ·
          refine ⟨57505604510744628405953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38337069673829752270635827 57505604510744628405953741)
          ·
            refine ⟨21564601691529235652232653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57505604510744628405953741 21564601691529235652232653)
            ·
              refine ⟨8086725634323463369587245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21564601691529235652232653 8086725634323463369587245)
              ·
                refine ⟨3032522112871298763595217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8086725634323463369587245 3032522112871298763595217)
                ·
                  refine ⟨2274391584653474072696413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032522112871298763595217 2274391584653474072696413)
                  ·
                    refine ⟨852896844245052777261155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274391584653474072696413 852896844245052777261155)
                    ·
                      rfl

theorem cell22_2491516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2491516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491516 prefixEnd_2491516 := by exact prefixLift 2491516
  have htrace : WordTrace (prefixWord ++ tailWord_2491516) baseStart_2491516 baseEnd_2491516 := by
    simpa [prefixWord, tailWord_2491516, baseEnd_2491516] using wordTrace_append hprefix tailTrace_2491516
  have hstable : (prefixWord ++ tailWord_2491516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491516).length < 2 ^ (prefixWord ++ tailWord_2491516).sum := by decide
  have hdescent : baseEnd_2491516 < baseStart_2491516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491550 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2491550 : Nat := 118140960795 + 2491550 * 2 ^ 59
def prefixEnd_2491550 : Nat := 4983230072969 + 3 ^ 40 * 2491550 * 2
def baseEnd_2491550 : Nat := 852908483139888021911051

theorem tailTrace_2491550 : CollatzResearch.WordTrace tailWord_2491550 prefixEnd_2491550 852908483139888021911051 := by
  unfold tailWord_2491550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359286765443418463438013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60582862749031565138336069 11359286765443418463438013)
  ·
    refine ⟨4259732537041281923789255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11359286765443418463438013 4259732537041281923789255)
    ·
      refine ⟨6389598805561922885683883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259732537041281923789255 6389598805561922885683883)
      ·
        refine ⟨9584398208342884328525825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6389598805561922885683883 9584398208342884328525825)
        ·
          refine ⟨7188298656257163246394369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9584398208342884328525825 7188298656257163246394369)
          ·
            refine ⟨5391223992192872434795777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7188298656257163246394369 5391223992192872434795777)
            ·
              refine ⟨4043417994144654326096833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391223992192872434795777 4043417994144654326096833)
              ·
                refine ⟨3032563495608490744572625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043417994144654326096833 3032563495608490744572625)
                ·
                  refine ⟨2274422621706368058429469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032563495608490744572625 2274422621706368058429469)
                  ·
                    refine ⟨852908483139888021911051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274422621706368058429469 852908483139888021911051)
                    ·
                      rfl

theorem cell22_2491550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2491550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491550 prefixEnd_2491550 := by exact prefixLift 2491550
  have htrace : WordTrace (prefixWord ++ tailWord_2491550) baseStart_2491550 baseEnd_2491550 := by
    simpa [prefixWord, tailWord_2491550, baseEnd_2491550] using wordTrace_append hprefix tailTrace_2491550
  have hstable : (prefixWord ++ tailWord_2491550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491550).length < 2 ^ (prefixWord ++ tailWord_2491550).sum := by decide
  have hdescent : baseEnd_2491550 < baseStart_2491550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491608 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_2491608 : Nat := 118140960795 + 2491608 * 2 ^ 59
def prefixEnd_2491608 : Nat := 4983230072969 + 3 ^ 40 * 2491608 * 2
def baseEnd_2491608 : Nat := 284309445908398401320291

theorem tailTrace_2491608 : CollatzResearch.WordTrace tailWord_2491608 prefixEnd_2491608 284309445908398401320291 := by
  unfold tailWord_2491608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45438204778668611806557739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60584273038224815742076985 45438204778668611806557739)
  ·
    refine ⟨68157307168002917709836609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45438204778668611806557739 68157307168002917709836609)
    ·
      refine ⟨51117980376002188282377457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68157307168002917709836609 51117980376002188282377457)
      ·
        refine ⟨38338485282001641211783093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51117980376002188282377457 38338485282001641211783093)
        ·
          refine ⟨3594232995187653863604665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38338485282001641211783093 3594232995187653863604665)
          ·
            refine ⟨2695674746390740397703499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594232995187653863604665 2695674746390740397703499)
            ·
              refine ⟨4043512119586110596555249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695674746390740397703499 4043512119586110596555249)
              ·
                refine ⟨3032634089689582947416437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043512119586110596555249 3032634089689582947416437)
                ·
                  refine ⟨284309445908398401320291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3032634089689582947416437 284309445908398401320291)
                  ·
                    rfl

theorem cell22_2491608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_2491608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491608 prefixEnd_2491608 := by exact prefixLift 2491608
  have htrace : WordTrace (prefixWord ++ tailWord_2491608) baseStart_2491608 baseEnd_2491608 := by
    simpa [prefixWord, tailWord_2491608, baseEnd_2491608] using wordTrace_append hprefix tailTrace_2491608
  have hstable : (prefixWord ++ tailWord_2491608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491608).length < 2 ^ (prefixWord ++ tailWord_2491608).sum := by decide
  have hdescent : baseEnd_2491608 < baseStart_2491608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491651 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 4, 3]
def baseStart_2491651 : Nat := 118140960795 + 2491651 * 2 ^ 59
def prefixEnd_2491651 : Nat := 4983230072969 + 3 ^ 40 * 2491651 * 2
def baseEnd_2491651 : Nat := 852943057503957425135741

theorem tailTrace_2491651 : CollatzResearch.WordTrace tailWord_2491651 prefixEnd_2491651 852943057503957425135741 := by
  unfold tailWord_2491651
  simp only [CollatzResearch.WordTrace]
  refine ⟨90877977896181441956930807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60585318597454294637953871 90877977896181441956930807)
  ·
    refine ⟨136316966844272162935396211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90877977896181441956930807 136316966844272162935396211)
    ·
      refine ⟨204475450266408244403094317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136316966844272162935396211 204475450266408244403094317)
      ·
        refine ⟨76678293849903091651160369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204475450266408244403094317 76678293849903091651160369)
        ·
          refine ⟨57508720387427318738370277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76678293849903091651160369 57508720387427318738370277)
          ·
            refine ⟨10782885072642622263444427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57508720387427318738370277 10782885072642622263444427)
            ·
              refine ⟨16174327608963933395166641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782885072642622263444427 16174327608963933395166641)
              ·
                refine ⟨12130745706722950046374981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16174327608963933395166641 12130745706722950046374981)
                ·
                  refine ⟨2274514820010553133695309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12130745706722950046374981 2274514820010553133695309)
                  ·
                    refine ⟨852943057503957425135741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274514820010553133695309 852943057503957425135741)
                    ·
                      rfl

theorem cell22_2491651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].length) (baseStart_2491651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491651 prefixEnd_2491651 := by exact prefixLift 2491651
  have htrace : WordTrace (prefixWord ++ tailWord_2491651) baseStart_2491651 baseEnd_2491651 := by
    simpa [prefixWord, tailWord_2491651, baseEnd_2491651] using wordTrace_append hprefix tailTrace_2491651
  have hstable : (prefixWord ++ tailWord_2491651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491651).length < 2 ^ (prefixWord ++ tailWord_2491651).sum := by decide
  have hdescent : baseEnd_2491651 < baseStart_2491651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491685 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_2491685 : Nat := 118140960795 + 2491685 * 2 ^ 59
def prefixEnd_2491685 : Nat := 4983230072969 + 3 ^ 40 * 2491685 * 2
def baseEnd_2491685 : Nat := 852954696398792669785637

theorem tailTrace_2491685 : CollatzResearch.WordTrace tailWord_2491685 prefixEnd_2491685 852954696398792669785637 := by
  unfold tailWord_2491685
  simp only [CollatzResearch.WordTrace]
  refine ⟨90879217978058265763668509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60586145318705510509112339 90879217978058265763668509)
  ·
    refine ⟨34079706741771849661375691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90879217978058265763668509 34079706741771849661375691)
    ·
      refine ⟨51119560112657774492063537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34079706741771849661375691 51119560112657774492063537)
      ·
        refine ⟨38339670084493330869047653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51119560112657774492063537 38339670084493330869047653)
        ·
          refine ⟨7188688140842499537946435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38339670084493330869047653 7188688140842499537946435)
          ·
            refine ⟨10783032211263749306919653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188688140842499537946435 10783032211263749306919653)
            ·
              refine ⟨2021818539611952995047435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10783032211263749306919653 2021818539611952995047435)
              ·
                refine ⟨3032727809417929492571153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021818539611952995047435 3032727809417929492571153)
                ·
                  refine ⟨2274545857063447119428365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032727809417929492571153 2274545857063447119428365)
                  ·
                    refine ⟨852954696398792669785637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274545857063447119428365 852954696398792669785637)
                    ·
                      rfl

theorem cell22_2491685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_2491685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491685 prefixEnd_2491685 := by exact prefixLift 2491685
  have htrace : WordTrace (prefixWord ++ tailWord_2491685) baseStart_2491685 baseEnd_2491685 := by
    simpa [prefixWord, tailWord_2491685, baseEnd_2491685] using wordTrace_append hprefix tailTrace_2491685
  have hstable : (prefixWord ++ tailWord_2491685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491685).length < 2 ^ (prefixWord ++ tailWord_2491685).sum := by decide
  have hdescent : baseEnd_2491685 < baseStart_2491685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491696 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_2491696 : Nat := 118140960795 + 2491696 * 2 ^ 59
def prefixEnd_2491696 : Nat := 4983230072969 + 3 ^ 40 * 2491696 * 2
def baseEnd_2491696 : Nat := 852958461923592307760603

theorem tailTrace_2491696 : CollatzResearch.WordTrace tailWord_2491696 prefixEnd_2491696 852958461923592307760603 := by
  unfold tailWord_2491696
  simp only [CollatzResearch.WordTrace]
  refine ⟨45439809590509207321159471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60586412787345609761545961 45439809590509207321159471)
  ·
    refine ⟨68159714385763810981739207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45439809590509207321159471 68159714385763810981739207)
    ·
      refine ⟨102239571578645716472608811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68159714385763810981739207 102239571578645716472608811)
      ·
        refine ⟨153359357367968574708913217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102239571578645716472608811 153359357367968574708913217)
        ·
          refine ⟨115019518025976431031684913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153359357367968574708913217 115019518025976431031684913)
          ·
            refine ⟨86264638519482323273763685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115019518025976431031684913 86264638519482323273763685)
            ·
              refine ⟨16174619722402935613830691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86264638519482323273763685 16174619722402935613830691)
              ·
                refine ⟨24261929583604403420746037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16174619722402935613830691 24261929583604403420746037)
                ·
                  refine ⟨2274555898462912820694941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24261929583604403420746037 2274555898462912820694941)
                  ·
                    refine ⟨852958461923592307760603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274555898462912820694941 852958461923592307760603)
                    ·
                      rfl

theorem cell22_2491696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_2491696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491696 prefixEnd_2491696 := by exact prefixLift 2491696
  have htrace : WordTrace (prefixWord ++ tailWord_2491696) baseStart_2491696 baseEnd_2491696 := by
    simpa [prefixWord, tailWord_2491696, baseEnd_2491696] using wordTrace_append hprefix tailTrace_2491696
  have hstable : (prefixWord ++ tailWord_2491696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491696).length < 2 ^ (prefixWord ++ tailWord_2491696).sum := by decide
  have hdescent : baseEnd_2491696 < baseStart_2491696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491773 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2491773 : Nat := 118140960795 + 2491773 * 2 ^ 59
def prefixEnd_2491773 : Nat := 4983230072969 + 3 ^ 40 * 2491773 * 2
def baseEnd_2491773 : Nat := 852984820597189773585367

theorem tailTrace_2491773 : CollatzResearch.WordTrace tailWord_2491773 prefixEnd_2491773 852984820597189773585367 := by
  unfold tailWord_2491773
  simp only [CollatzResearch.WordTrace]
  refine ⟨90882427601739456792871973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60588285067826304528581315 90882427601739456792871973)
  ·
    refine ⟨17040455175326148148663495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90882427601739456792871973 17040455175326148148663495)
    ·
      refine ⟨25560682762989222222995243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17040455175326148148663495 25560682762989222222995243)
      ·
        refine ⟨38341024144483833334492865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25560682762989222222995243 38341024144483833334492865)
        ·
          refine ⟨28755768108362875000869649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38341024144483833334492865 28755768108362875000869649)
          ·
            refine ⟨21566826081272156250652237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28755768108362875000869649 21566826081272156250652237)
            ·
              refine ⟨8087559780477058593994589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21566826081272156250652237 8087559780477058593994589)
              ·
                refine ⟨3032834917678896972747971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8087559780477058593994589 3032834917678896972747971)
                ·
                  refine ⟨4549252376518345459121957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032834917678896972747971 4549252376518345459121957)
                  ·
                    refine ⟨852984820597189773585367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4549252376518345459121957 852984820597189773585367)
                    ·
                      rfl

theorem cell22_2491773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2491773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491773 prefixEnd_2491773 := by exact prefixLift 2491773
  have htrace : WordTrace (prefixWord ++ tailWord_2491773) baseStart_2491773 baseEnd_2491773 := by
    simpa [prefixWord, tailWord_2491773, baseEnd_2491773] using wordTrace_append hprefix tailTrace_2491773
  have hstable : (prefixWord ++ tailWord_2491773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491773).length < 2 ^ (prefixWord ++ tailWord_2491773).sum := by decide
  have hdescent : baseEnd_2491773 < baseStart_2491773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491777 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 5]
def baseStart_2491777 : Nat := 118140960795 + 2491777 * 2 ^ 59
def prefixEnd_2491777 : Nat := 4983230072969 + 3 ^ 40 * 2491777 * 2
def baseEnd_2491777 : Nat := 284328729959645032161785

theorem tailTrace_2491777 : CollatzResearch.WordTrace tailWord_2491777 prefixEnd_2491777 284328729959645032161785 := by
  unfold tailWord_2491777
  simp only [CollatzResearch.WordTrace]
  refine ⟨90882573493724965476017585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60588382329149976984011723 90882573493724965476017585)
  ·
    refine ⟨68161930120293724107013189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90882573493724965476017585 68161930120293724107013189)
    ·
      refine ⟨12780361897555073270064973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68161930120293724107013189 12780361897555073270064973)
      ·
        refine ⟨4792635711583152476274365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12780361897555073270064973 4792635711583152476274365)
        ·
          refine ⟨1797238391843682178602887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4792635711583152476274365 1797238391843682178602887)
          ·
            refine ⟨2695857587765523267904331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797238391843682178602887 2695857587765523267904331)
            ·
              refine ⟨4043786381648284901856497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695857587765523267904331 4043786381648284901856497)
              ·
                refine ⟨3032839786236213676392373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043786381648284901856497 3032839786236213676392373)
                ·
                  refine ⟨284328729959645032161785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3032839786236213676392373 284328729959645032161785)
                  ·
                    rfl

theorem cell22_2491777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_2491777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491777 prefixEnd_2491777 := by exact prefixLift 2491777
  have htrace : WordTrace (prefixWord ++ tailWord_2491777) baseStart_2491777 baseEnd_2491777 := by
    simpa [prefixWord, tailWord_2491777, baseEnd_2491777] using wordTrace_append hprefix tailTrace_2491777
  have hstable : (prefixWord ++ tailWord_2491777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491777).length < 2 ^ (prefixWord ++ tailWord_2491777).sum := by decide
  have hdescent : baseEnd_2491777 < baseStart_2491777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491788 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_2491788 : Nat := 118140960795 + 2491788 * 2 ^ 59
def prefixEnd_2491788 : Nat := 4983230072969 + 3 ^ 40 * 2491788 * 2
def baseEnd_2491788 : Nat := 284329985134578244820107

theorem tailTrace_2491788 : CollatzResearch.WordTrace tailWord_2491788 prefixEnd_2491788 284329985134578244820107 := by
  unfold tailWord_2491788
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441487348342557177334009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60588649797790076236445345 45441487348342557177334009)
  ·
    refine ⟨34081115511256917883000507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45441487348342557177334009 34081115511256917883000507)
    ·
      refine ⟨51121673266885376824500761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34081115511256917883000507 51121673266885376824500761)
      ·
        refine ⟨38341254950164032618375571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51121673266885376824500761 38341254950164032618375571)
        ·
          refine ⟨57511882425246048927563357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38341254950164032618375571 57511882425246048927563357)
          ·
            refine ⟨21566955909467268347836259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57511882425246048927563357 21566955909467268347836259)
            ·
              refine ⟨32350433864200902521754389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21566955909467268347836259 32350433864200902521754389)
              ·
                refine ⟨1516426587384417305707237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32350433864200902521754389 1516426587384417305707237)
                ·
                  refine ⟨284329985134578244820107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516426587384417305707237 284329985134578244820107)
                  ·
                    rfl

theorem cell22_2491788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_2491788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491788 prefixEnd_2491788 := by exact prefixLift 2491788
  have htrace : WordTrace (prefixWord ++ tailWord_2491788) baseStart_2491788 baseEnd_2491788 := by
    simpa [prefixWord, tailWord_2491788, baseEnd_2491788] using wordTrace_append hprefix tailTrace_2491788
  have hstable : (prefixWord ++ tailWord_2491788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491788).length < 2 ^ (prefixWord ++ tailWord_2491788).sum := by decide
  have hdescent : baseEnd_2491788 < baseStart_2491788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491801 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2491801 : Nat := 118140960795 + 2491801 * 2 ^ 59
def prefixEnd_2491801 : Nat := 4983230072969 + 3 ^ 40 * 2491801 * 2
def baseEnd_2491801 : Nat := 852994405569407033885281

theorem tailTrace_2491801 : CollatzResearch.WordTrace tailWord_2491801 prefixEnd_2491801 852994405569407033885281 := by
  unfold tailWord_2491801
  simp only [CollatzResearch.WordTrace]
  refine ⟨90883448845638017574891257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60588965897092011716594171 90883448845638017574891257)
  ·
    refine ⟨68162586634228513181168443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90883448845638017574891257 68162586634228513181168443)
    ·
      refine ⟨102243879951342769771752665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68162586634228513181168443 102243879951342769771752665)
      ·
        refine ⟨76682909963507077328814499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102243879951342769771752665 76682909963507077328814499)
        ·
          refine ⟨115024364945260615993221749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76682909963507077328814499 115024364945260615993221749)
          ·
            refine ⟨10783534213618182749364539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115024364945260615993221749 10783534213618182749364539)
            ·
              refine ⟨16175301320427274124046809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10783534213618182749364539 16175301320427274124046809)
              ·
                refine ⟨12131475990320455593035107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16175301320427274124046809 12131475990320455593035107)
                ·
                  refine ⟨18197213985480683389552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131475990320455593035107 18197213985480683389552661)
                  ·
                    refine ⟨852994405569407033885281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18197213985480683389552661 852994405569407033885281)
                    ·
                      rfl

theorem cell22_2491801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2491801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491801 prefixEnd_2491801 := by exact prefixLift 2491801
  have htrace : WordTrace (prefixWord ++ tailWord_2491801) baseStart_2491801 baseEnd_2491801 := by
    simpa [prefixWord, tailWord_2491801, baseEnd_2491801] using wordTrace_append hprefix tailTrace_2491801
  have hstable : (prefixWord ++ tailWord_2491801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491801).length < 2 ^ (prefixWord ++ tailWord_2491801).sum := by decide
  have hdescent : baseEnd_2491801 < baseStart_2491801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491833 : List Nat := [1, 2, 1, 4, 4, 2, 8]
def baseStart_2491833 : Nat := 118140960795 + 2491833 * 2 ^ 59
def prefixEnd_2491833 : Nat := 4983230072969 + 3 ^ 40 * 2491833 * 2
def baseEnd_2491833 : Nat := 31592791104569245077229

theorem tailTrace_2491833 : CollatzResearch.WordTrace tailWord_2491833 prefixEnd_2491833 31592791104569245077229 := by
  unfold tailWord_2491833
  simp only [CollatzResearch.WordTrace]
  refine ⟨90884615981522087040056153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60589743987681391360037435 90884615981522087040056153)
  ·
    refine ⟨68163461986141565280042115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90884615981522087040056153 68163461986141565280042115)
    ·
      refine ⟨102245192979212347920063173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68163461986141565280042115 102245192979212347920063173)
      ·
        refine ⟨19170973683602315235011845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102245192979212347920063173 19170973683602315235011845)
        ·
          refine ⟨3594557565675434106564721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19170973683602315235011845 3594557565675434106564721)
          ·
            refine ⟨2695918174256575579923541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594557565675434106564721 2695918174256575579923541)
            ·
              refine ⟨31592791104569245077229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2695918174256575579923541 31592791104569245077229)
              ·
                rfl

theorem cell22_2491833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 8].length) (baseStart_2491833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491833 prefixEnd_2491833 := by exact prefixLift 2491833
  have htrace : WordTrace (prefixWord ++ tailWord_2491833) baseStart_2491833 baseEnd_2491833 := by
    simpa [prefixWord, tailWord_2491833, baseEnd_2491833] using wordTrace_append hprefix tailTrace_2491833
  have hstable : (prefixWord ++ tailWord_2491833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491833).length < 2 ^ (prefixWord ++ tailWord_2491833).sum := by decide
  have hdescent : baseEnd_2491833 < baseStart_2491833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491923 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 6]
def baseStart_2491923 : Nat := 118140960795 + 2491923 * 2 ^ 59
def prefixEnd_2491923 : Nat := 4983230072969 + 3 ^ 40 * 2491923 * 2
def baseEnd_2491923 : Nat := 284345389554213127444969

theorem tailTrace_2491923 : CollatzResearch.WordTrace tailWord_2491923 prefixEnd_2491923 284345389554213127444969 := by
  unfold tailWord_2491923
  simp only [CollatzResearch.WordTrace]
  refine ⟨90887898551196032410832423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60591932367464021607221615 90887898551196032410832423)
  ·
    refine ⟨136331847826794048616248635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90887898551196032410832423 136331847826794048616248635)
    ·
      refine ⟨204497771740191072924372953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136331847826794048616248635 204497771740191072924372953)
      ·
        refine ⟨153373328805143304693279715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204497771740191072924372953 153373328805143304693279715)
        ·
          refine ⟨230059993207714957039919573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153373328805143304693279715 230059993207714957039919573)
          ·
            refine ⟨5392031090805819305623115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 230059993207714957039919573 5392031090805819305623115)
            ·
              refine ⟨8088046636208728958434673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392031090805819305623115 8088046636208728958434673)
              ·
                refine ⟨6066034977156546718826005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8088046636208728958434673 6066034977156546718826005)
                ·
                  refine ⟨284345389554213127444969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6066034977156546718826005 284345389554213127444969)
                  ·
                    rfl

theorem cell22_2491923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_2491923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491923 prefixEnd_2491923 := by exact prefixLift 2491923
  have htrace : WordTrace (prefixWord ++ tailWord_2491923) baseStart_2491923 baseEnd_2491923 := by
    simpa [prefixWord, tailWord_2491923, baseEnd_2491923] using wordTrace_append hprefix tailTrace_2491923
  have hstable : (prefixWord ++ tailWord_2491923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491923).length < 2 ^ (prefixWord ++ tailWord_2491923).sum := by decide
  have hdescent : baseEnd_2491923 < baseStart_2491923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491953 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2491953 : Nat := 118140960795 + 2491953 * 2 ^ 59
def prefixEnd_2491953 : Nat := 4983230072969 + 3 ^ 40 * 2491953 * 2
def baseEnd_2491953 : Nat := 853046438275729304084815

theorem tailTrace_2491953 : CollatzResearch.WordTrace tailWord_2491953 prefixEnd_2491953 853046438275729304084815 := by
  unfold tailWord_2491953
  simp only [CollatzResearch.WordTrace]
  refine ⟨90888992741087347534424513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60592661827391565022949675 90888992741087347534424513)
  ·
    refine ⟨68166744555815510650818385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90888992741087347534424513 68166744555815510650818385)
    ·
      refine ⟨51125058416861632988113789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68166744555815510650818385 51125058416861632988113789)
      ·
        refine ⟨19171896906323112370542671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51125058416861632988113789 19171896906323112370542671)
        ·
          refine ⟨28757845359484668555814007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19171896906323112370542671 28757845359484668555814007)
          ·
            refine ⟨43136768039227002833721011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28757845359484668555814007 43136768039227002833721011)
            ·
              refine ⟨64705152058840504250581517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43136768039227002833721011 64705152058840504250581517)
              ·
                refine ⟨24264432022065189093968069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64705152058840504250581517 24264432022065189093968069)
                ·
                  refine ⟨4549581004137222955119013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24264432022065189093968069 4549581004137222955119013)
                  ·
                    refine ⟨853046438275729304084815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4549581004137222955119013 853046438275729304084815)
                    ·
                      rfl

theorem cell22_2491953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2491953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491953 prefixEnd_2491953 := by exact prefixLift 2491953
  have htrace : WordTrace (prefixWord ++ tailWord_2491953) baseStart_2491953 baseEnd_2491953 := by
    simpa [prefixWord, tailWord_2491953, baseEnd_2491953] using wordTrace_append hprefix tailTrace_2491953
  have hstable : (prefixWord ++ tailWord_2491953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491953).length < 2 ^ (prefixWord ++ tailWord_2491953).sum := by decide
  have hdescent : baseEnd_2491953 < baseStart_2491953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491955 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 4, 3]
def baseStart_2491955 : Nat := 118140960795 + 2491955 * 2 ^ 59
def prefixEnd_2491955 : Nat := 4983230072969 + 3 ^ 40 * 2491955 * 2
def baseEnd_2491955 : Nat := 853047122916601965534809

theorem tailTrace_2491955 : CollatzResearch.WordTrace tailWord_2491955 prefixEnd_2491955 853047122916601965534809 := by
  unfold tailWord_2491955
  simp only [CollatzResearch.WordTrace]
  refine ⟨90889065687080101875997319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60592710458053401250664879 90889065687080101875997319)
  ·
    refine ⟨136333598530620152813995979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90889065687080101875997319 136333598530620152813995979)
    ·
      refine ⟨204500397795930229220993969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136333598530620152813995979 204500397795930229220993969)
      ·
        refine ⟨153375298346947671915745477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204500397795930229220993969 153375298346947671915745477)
        ·
          refine ⟨28757868440052688484202277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153375298346947671915745477 28757868440052688484202277)
          ·
            refine ⟨5392100332509879090787927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28757868440052688484202277 5392100332509879090787927)
            ·
              refine ⟨8088150498764818636181891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392100332509879090787927 8088150498764818636181891)
              ·
                refine ⟨12132225748147227954272837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8088150498764818636181891 12132225748147227954272837)
                ·
                  refine ⟨2274792327777605241426157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12132225748147227954272837 2274792327777605241426157)
                  ·
                    refine ⟨853047122916601965534809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274792327777605241426157 853047122916601965534809)
                    ·
                      rfl

theorem cell22_2491955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].length) (baseStart_2491955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2491955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2491955 prefixEnd_2491955 := by exact prefixLift 2491955
  have htrace : WordTrace (prefixWord ++ tailWord_2491955) baseStart_2491955 baseEnd_2491955 := by
    simpa [prefixWord, tailWord_2491955, baseEnd_2491955] using wordTrace_append hprefix tailTrace_2491955
  have hstable : (prefixWord ++ tailWord_2491955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491955).length < 2 ^ (prefixWord ++ tailWord_2491955).sum := by decide
  have hdescent : baseEnd_2491955 < baseStart_2491955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492017 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_2492017 : Nat := 118140960795 + 2492017 * 2 ^ 59
def prefixEnd_2492017 : Nat := 4983230072969 + 3 ^ 40 * 2492017 * 2
def baseEnd_2492017 : Nat := 853068346783654470484619

theorem tailTrace_2492017 : CollatzResearch.WordTrace tailWord_2492017 prefixEnd_2492017 853068346783654470484619 := by
  unfold tailWord_2492017
  simp only [CollatzResearch.WordTrace]
  refine ⟨90891327012855486464754305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60594218008570324309836203 90891327012855486464754305)
  ·
    refine ⟨68168495259641614848565729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90891327012855486464754305 68168495259641614848565729)
    ·
      refine ⟨51126371444731211136424297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68168495259641614848565729 51126371444731211136424297)
      ·
        refine ⟨38344778583548408352318223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51126371444731211136424297 38344778583548408352318223)
        ·
          refine ⟨57517167875322612528477335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38344778583548408352318223 57517167875322612528477335)
          ·
            refine ⟨86275751812983918792716003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57517167875322612528477335 86275751812983918792716003)
            ·
              refine ⟨129413627719475878189074005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86275751812983918792716003 129413627719475878189074005)
              ·
                refine ⟨1516565949837607947528211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 129413627719475878189074005 1516565949837607947528211)
                ·
                  refine ⟨2274848924756411921292317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516565949837607947528211 2274848924756411921292317)
                  ·
                    refine ⟨853068346783654470484619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274848924756411921292317 853068346783654470484619)
                    ·
                      rfl

theorem cell22_2492017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_2492017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492017 prefixEnd_2492017 := by exact prefixLift 2492017
  have htrace : WordTrace (prefixWord ++ tailWord_2492017) baseStart_2492017 baseEnd_2492017 := by
    simpa [prefixWord, tailWord_2492017, baseEnd_2492017] using wordTrace_append hprefix tailTrace_2492017
  have hstable : (prefixWord ++ tailWord_2492017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492017).length < 2 ^ (prefixWord ++ tailWord_2492017).sum := by decide
  have hdescent : baseEnd_2492017 < baseStart_2492017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492028 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2492028 : Nat := 118140960795 + 2492028 * 2 ^ 59
def prefixEnd_2492028 : Nat := 4983230072969 + 3 ^ 40 * 2492028 * 2
def baseEnd_2492028 : Nat := 853072112308454108459585

theorem tailTrace_2492028 : CollatzResearch.WordTrace tailWord_2492028 prefixEnd_2492028 853072112308454108459585 := by
  unfold tailWord_2492028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45445864107907817671702369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60594485477210423562269825 45445864107907817671702369)
  ·
    refine ⟨34084398080930863253776777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45445864107907817671702369 34084398080930863253776777)
    ·
      refine ⟨25563298560698147440332583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34084398080930863253776777 25563298560698147440332583)
      ·
        refine ⟨38344947841047221160498875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25563298560698147440332583 38344947841047221160498875)
        ·
          refine ⟨57517421761570831740748313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38344947841047221160498875 57517421761570831740748313)
          ·
            refine ⟨43138066321178123805561235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57517421761570831740748313 43138066321178123805561235)
            ·
              refine ⟨64707099481767185708341853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43138066321178123805561235 64707099481767185708341853)
              ·
                refine ⟨24265162305662694640628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64707099481767185708341853 24265162305662694640628195)
                ·
                  refine ⟨36397743458494041960942293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24265162305662694640628195 36397743458494041960942293)
                  ·
                    refine ⟨853072112308454108459585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36397743458494041960942293 853072112308454108459585)
                    ·
                      rfl

theorem cell22_2492028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2492028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492028 prefixEnd_2492028 := by exact prefixLift 2492028
  have htrace : WordTrace (prefixWord ++ tailWord_2492028) baseStart_2492028 baseEnd_2492028 := by
    simpa [prefixWord, tailWord_2492028, baseEnd_2492028] using wordTrace_append hprefix tailTrace_2492028
  have hstable : (prefixWord ++ tailWord_2492028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492028).length < 2 ^ (prefixWord ++ tailWord_2492028).sum := by decide
  have hdescent : baseEnd_2492028 < baseStart_2492028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492090 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_2492090 : Nat := 118140960795 + 2492090 * 2 ^ 59
def prefixEnd_2492090 : Nat := 4983230072969 + 3 ^ 40 * 2492090 * 2
def baseEnd_2492090 : Nat := 853093336175506613409395

theorem tailTrace_2492090 : CollatzResearch.WordTrace tailWord_2492090 prefixEnd_2492090 853093336175506613409395 := by
  unfold tailWord_2492090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22723497385397754983040431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60595993027727346621441149 22723497385397754983040431)
  ·
    refine ⟨34085246078096632474560647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22723497385397754983040431 34085246078096632474560647)
    ·
      refine ⟨51127869117144948711840971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34085246078096632474560647 51127869117144948711840971)
      ·
        refine ⟨76691803675717423067761457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51127869117144948711840971 76691803675717423067761457)
        ·
          refine ⟨57518852756788067300821093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76691803675717423067761457 57518852756788067300821093)
          ·
            refine ⟨10784784891897762618903955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57518852756788067300821093 10784784891897762618903955)
            ·
              refine ⟨16177177337846643928355933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10784784891897762618903955 16177177337846643928355933)
              ·
                refine ⟨6066441501692491473133475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16177177337846643928355933 6066441501692491473133475)
                ·
                  refine ⟨9099662252538737209700213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066441501692491473133475 9099662252538737209700213)
                  ·
                    refine ⟨853093336175506613409395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9099662252538737209700213 853093336175506613409395)
                    ·
                      rfl

theorem cell22_2492090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_2492090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492090 prefixEnd_2492090 := by exact prefixLift 2492090
  have htrace : WordTrace (prefixWord ++ tailWord_2492090) baseStart_2492090 baseEnd_2492090 := by
    simpa [prefixWord, tailWord_2492090, baseEnd_2492090] using wordTrace_append hprefix tailTrace_2492090
  have hstable : (prefixWord ++ tailWord_2492090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492090).length < 2 ^ (prefixWord ++ tailWord_2492090).sum := by decide
  have hdescent : baseEnd_2492090 < baseStart_2492090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492141 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_2492141 : Nat := 118140960795 + 2492141 * 2 ^ 59
def prefixEnd_2492141 : Nat := 4983230072969 + 3 ^ 40 * 2492141 * 2
def baseEnd_2492141 : Nat := 853110794517759480384239

theorem tailTrace_2492141 : CollatzResearch.WordTrace tailWord_2492141 prefixEnd_2492141 853110794517759480384239 := by
  unfold tailWord_2492141
  simp only [CollatzResearch.WordTrace]
  refine ⟨90895849664406255642268277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60597233109604170428178851 90895849664406255642268277)
  ·
    refine ⟨8521485906038086466462651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90895849664406255642268277 8521485906038086466462651)
    ·
      refine ⟨12782228859057129699693977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521485906038086466462651 12782228859057129699693977)
      ·
        refine ⟨9586671644292847274770483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12782228859057129699693977 9586671644292847274770483)
        ·
          refine ⟨14380007466439270912155725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586671644292847274770483 14380007466439270912155725)
          ·
            refine ⟨5392502799914726592058397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14380007466439270912155725 5392502799914726592058397)
            ·
              refine ⟨2022188549968022472021899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5392502799914726592058397 2022188549968022472021899)
              ·
                refine ⟨3033282824952033708032849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022188549968022472021899 3033282824952033708032849)
                ·
                  refine ⟨2274962118714025281024637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3033282824952033708032849 2274962118714025281024637)
                  ·
                    refine ⟨853110794517759480384239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274962118714025281024637 853110794517759480384239)
                    ·
                      rfl

theorem cell22_2492141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_2492141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492141 prefixEnd_2492141 := by exact prefixLift 2492141
  have htrace : WordTrace (prefixWord ++ tailWord_2492141) baseStart_2492141 baseEnd_2492141 := by
    simpa [prefixWord, tailWord_2492141, baseEnd_2492141] using wordTrace_append hprefix tailTrace_2492141
  have hstable : (prefixWord ++ tailWord_2492141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492141).length < 2 ^ (prefixWord ++ tailWord_2492141).sum := by decide
  have hdescent : baseEnd_2492141 < baseStart_2492141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492229 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_2492229 : Nat := 118140960795 + 2492229 * 2 ^ 59
def prefixEnd_2492229 : Nat := 4983230072969 + 3 ^ 40 * 2492229 * 2
def baseEnd_2492229 : Nat := 853140918716156584183969

theorem tailTrace_2492229 : CollatzResearch.WordTrace tailWord_2492229 prefixEnd_2492229 853140918716156584183969 := by
  unfold tailWord_2492229
  simp only [CollatzResearch.WordTrace]
  refine ⟨90899059288087446671471741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60599372858724964447647827 90899059288087446671471741)
  ·
    refine ⟨34087147233032792501801903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90899059288087446671471741 34087147233032792501801903)
    ·
      refine ⟨51130720849549188752702855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34087147233032792501801903 51130720849549188752702855)
      ·
        refine ⟨76696081274323783129054283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51130720849549188752702855 76696081274323783129054283)
        ·
          refine ⟨115044121911485674693581425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76696081274323783129054283 115044121911485674693581425)
          ·
            refine ⟨86283091433614256020186069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115044121911485674693581425 86283091433614256020186069)
            ·
              refine ⟨2022259955475334125473111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86283091433614256020186069 2022259955475334125473111)
              ·
                refine ⟨3033389933213001188209667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022259955475334125473111 3033389933213001188209667)
                ·
                  refine ⟨4550084899819501782314501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033389933213001188209667 4550084899819501782314501)
                  ·
                    refine ⟨853140918716156584183969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550084899819501782314501 853140918716156584183969)
                    ·
                      rfl

theorem cell22_2492229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_2492229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492229 prefixEnd_2492229 := by exact prefixLift 2492229
  have htrace : WordTrace (prefixWord ++ tailWord_2492229) baseStart_2492229 baseEnd_2492229 := by
    simpa [prefixWord, tailWord_2492229, baseEnd_2492229] using wordTrace_append hprefix tailTrace_2492229
  have hstable : (prefixWord ++ tailWord_2492229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492229).length < 2 ^ (prefixWord ++ tailWord_2492229).sum := by decide
  have hdescent : baseEnd_2492229 < baseStart_2492229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492240 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_2492240 : Nat := 118140960795 + 2492240 * 2 ^ 59
def prefixEnd_2492240 : Nat := 4983230072969 + 3 ^ 40 * 2492240 * 2
def baseEnd_2492240 : Nat := 853144684240956222158935

theorem tailTrace_2492240 : CollatzResearch.WordTrace tailWord_2492240 prefixEnd_2492240 853144684240956222158935 := by
  unfold tailWord_2492240
  simp only [CollatzResearch.WordTrace]
  refine ⟨45449730245523797775061087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60599640327365063700081449 45449730245523797775061087)
  ·
    refine ⟨68174595368285696662591631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45449730245523797775061087 68174595368285696662591631)
    ·
      refine ⟨102261893052428544993887447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68174595368285696662591631 102261893052428544993887447)
      ·
        refine ⟨153392839578642817490831171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102261893052428544993887447 153392839578642817490831171)
        ·
          refine ⟨230089259367964226236246757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153392839578642817490831171 230089259367964226236246757)
          ·
            refine ⟨43141736131493292419296267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230089259367964226236246757 43141736131493292419296267)
            ·
              refine ⟨64712604197239938628944401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43141736131493292419296267 64712604197239938628944401)
              ·
                refine ⟨48534453147929953971708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64712604197239938628944401 48534453147929953971708301)
                ·
                  refine ⟨18200419930473732739390613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48534453147929953971708301 18200419930473732739390613)
                  ·
                    refine ⟨853144684240956222158935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18200419930473732739390613 853144684240956222158935)
                    ·
                      rfl

theorem cell22_2492240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_2492240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492240 prefixEnd_2492240 := by exact prefixLift 2492240
  have htrace : WordTrace (prefixWord ++ tailWord_2492240) baseStart_2492240 baseEnd_2492240 := by
    simpa [prefixWord, tailWord_2492240, baseEnd_2492240] using wordTrace_append hprefix tailTrace_2492240
  have hstable : (prefixWord ++ tailWord_2492240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492240).length < 2 ^ (prefixWord ++ tailWord_2492240).sum := by decide
  have hdescent : baseEnd_2492240 < baseStart_2492240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492259 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_2492259 : Nat := 118140960795 + 2492259 * 2 ^ 59
def prefixEnd_2492259 : Nat := 4983230072969 + 3 ^ 40 * 2492259 * 2
def baseEnd_2492259 : Nat := 853151188329246505933877

theorem tailTrace_2492259 : CollatzResearch.WordTrace tailWord_2492259 prefixEnd_2492259 853151188329246505933877 := by
  unfold tailWord_2492259
  simp only [CollatzResearch.WordTrace]
  refine ⟨90900153477978761795063831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60600102318652507863375887 90900153477978761795063831)
  ·
    refine ⟨136350230216968142692595747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90900153477978761795063831 136350230216968142692595747)
    ·
      refine ⟨204525345325452214038893621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136350230216968142692595747 204525345325452214038893621)
      ·
        refine ⟨19174251124261145066146277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204525345325452214038893621 19174251124261145066146277)
        ·
          refine ⟨3595172085798964699902427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19174251124261145066146277 3595172085798964699902427)
          ·
            refine ⟨5392758128698447049853641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595172085798964699902427 5392758128698447049853641)
            ·
              refine ⟨4044568596523835287390231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392758128698447049853641 4044568596523835287390231)
              ·
                refine ⟨6066852894785752931085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044568596523835287390231 6066852894785752931085347)
                ·
                  refine ⟨9100279342178629396628021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066852894785752931085347 9100279342178629396628021)
                  ·
                    refine ⟨853151188329246505933877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9100279342178629396628021 853151188329246505933877)
                    ·
                      rfl

theorem cell22_2492259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_2492259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492259 prefixEnd_2492259 := by exact prefixLift 2492259
  have htrace : WordTrace (prefixWord ++ tailWord_2492259) baseStart_2492259 baseEnd_2492259 := by
    simpa [prefixWord, tailWord_2492259, baseEnd_2492259] using wordTrace_append hprefix tailTrace_2492259
  have hstable : (prefixWord ++ tailWord_2492259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492259).length < 2 ^ (prefixWord ++ tailWord_2492259).sum := by decide
  have hdescent : baseEnd_2492259 < baseStart_2492259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492278 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2492278 : Nat := 118140960795 + 2492278 * 2 ^ 59
def prefixEnd_2492278 : Nat := 4983230072969 + 3 ^ 40 * 2492278 * 2
def baseEnd_2492278 : Nat := 284385897472512263236273

theorem tailTrace_2492278 : CollatzResearch.WordTrace tailWord_2492278 prefixEnd_2492278 284385897472512263236273 := by
  unfold tailWord_2492278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681302904056870502500343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60600564309939952026670325 5681302904056870502500343)
  ·
    refine ⟨8521954356085305753750515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681302904056870502500343 8521954356085305753750515)
    ·
      refine ⟨12782931534127958630625773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521954356085305753750515 12782931534127958630625773)
      ·
        refine ⟨4793599325297984486484665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12782931534127958630625773 4793599325297984486484665)
        ·
          refine ⟨3595199493973488364863499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793599325297984486484665 3595199493973488364863499)
          ·
            refine ⟨5392799240960232547295249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595199493973488364863499 5392799240960232547295249)
            ·
              refine ⟨4044599430720174410471437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392799240960232547295249 4044599430720174410471437)
              ·
                refine ⟨1516724786520065403926789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4044599430720174410471437 1516724786520065403926789)
                ·
                  refine ⟨284385897472512263236273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516724786520065403926789 284385897472512263236273)
                  ·
                    rfl

theorem cell22_2492278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2492278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492278 prefixEnd_2492278 := by exact prefixLift 2492278
  have htrace : WordTrace (prefixWord ++ tailWord_2492278) baseStart_2492278 baseEnd_2492278 := by
    simpa [prefixWord, tailWord_2492278, baseEnd_2492278] using wordTrace_append hprefix tailTrace_2492278
  have hstable : (prefixWord ++ tailWord_2492278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492278).length < 2 ^ (prefixWord ++ tailWord_2492278).sum := by decide
  have hdescent : baseEnd_2492278 < baseStart_2492278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492287 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 7, 3]
def baseStart_2492287 : Nat := 118140960795 + 2492287 * 2 ^ 59
def prefixEnd_2492287 : Nat := 4983230072969 + 3 ^ 40 * 2492287 * 2
def baseEnd_2492287 : Nat := 853160773301463766233791

theorem tailTrace_2492287 : CollatzResearch.WordTrace tailWord_2492287 prefixEnd_2492287 853160773301463766233791 := by
  unfold tailWord_2492287
  simp only [CollatzResearch.WordTrace]
  refine ⟨90901174721877322577083115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60600783147918215051388743 90901174721877322577083115)
  ·
    refine ⟨136351762082815983865624673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90901174721877322577083115 136351762082815983865624673)
    ·
      refine ⟨102263821562111987899218505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136351762082815983865624673 102263821562111987899218505)
      ·
        refine ⟨76697866171583990924413879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102263821562111987899218505 76697866171583990924413879)
        ·
          refine ⟨115046799257375986386620819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76697866171583990924413879 115046799257375986386620819)
          ·
            refine ⟨172570198886063979579931229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115046799257375986386620819 172570198886063979579931229)
            ·
              refine ⟨64713824582273992342474211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172570198886063979579931229 64713824582273992342474211)
              ·
                refine ⟨97070736873410988513711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64713824582273992342474211 97070736873410988513711317)
                ·
                  refine ⟨2275095395470570043290109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97070736873410988513711317 2275095395470570043290109)
                  ·
                    refine ⟨853160773301463766233791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275095395470570043290109 853160773301463766233791)
                    ·
                      rfl

theorem cell22_2492287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_2492287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492287 prefixEnd_2492287 := by exact prefixLift 2492287
  have htrace : WordTrace (prefixWord ++ tailWord_2492287) baseStart_2492287 baseEnd_2492287 := by
    simpa [prefixWord, tailWord_2492287, baseEnd_2492287] using wordTrace_append hprefix tailTrace_2492287
  have hstable : (prefixWord ++ tailWord_2492287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492287).length < 2 ^ (prefixWord ++ tailWord_2492287).sum := by decide
  have hdescent : baseEnd_2492287 < baseStart_2492287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492289 : List Nat := [1, 2, 4, 4, 1, 1, 9]
def baseStart_2492289 : Nat := 118140960795 + 2492289 * 2 ^ 59
def prefixEnd_2492289 : Nat := 4983230072969 + 3 ^ 40 * 2492289 * 2
def baseEnd_2492289 : Nat := 31598572516382830654955

theorem tailTrace_2492289 : CollatzResearch.WordTrace tailWord_2492289 prefixEnd_2492289 31598572516382830654955 := by
  unfold tailWord_2492289
  simp only [CollatzResearch.WordTrace]
  refine ⟨90901247667870076918655921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60600831778580051279103947 90901247667870076918655921)
  ·
    refine ⟨68175935750902557688991941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90901247667870076918655921 68175935750902557688991941)
    ·
      refine ⟨12782987953294229566685989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68175935750902557688991941 12782987953294229566685989)
      ·
        refine ⟨2396810241242668043753623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12782987953294229566685989 2396810241242668043753623)
        ·
          refine ⟨3595215361864002065630435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396810241242668043753623 3595215361864002065630435)
          ·
            refine ⟨5392823042796003098445653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595215361864002065630435 5392823042796003098445653)
            ·
              refine ⟨31598572516382830654955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5392823042796003098445653 31598572516382830654955)
              ·
                rfl

theorem cell22_2492289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 9].length) (baseStart_2492289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492289 prefixEnd_2492289 := by exact prefixLift 2492289
  have htrace : WordTrace (prefixWord ++ tailWord_2492289) baseStart_2492289 baseEnd_2492289 := by
    simpa [prefixWord, tailWord_2492289, baseEnd_2492289] using wordTrace_append hprefix tailTrace_2492289
  have hstable : (prefixWord ++ tailWord_2492289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492289).length < 2 ^ (prefixWord ++ tailWord_2492289).sum := by decide
  have hdescent : baseEnd_2492289 < baseStart_2492289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492310 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2492310 : Nat := 118140960795 + 2492310 * 2 ^ 59
def prefixEnd_2492310 : Nat := 4983230072969 + 3 ^ 40 * 2492310 * 2
def baseEnd_2492310 : Nat := 853168646671499372908721

theorem tailTrace_2492310 : CollatzResearch.WordTrace tailWord_2492310 prefixEnd_2492310 853168646671499372908721 := by
  unfold tailWord_2492310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681375850049624844073149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60601342400529331670113589 5681375850049624844073149)
  ·
    refine ⟨2130515943768609316527431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5681375850049624844073149 2130515943768609316527431)
    ·
      refine ⟨3195773915652913974791147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130515943768609316527431 3195773915652913974791147)
      ·
        refine ⟨4793660873479370962186721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195773915652913974791147 4793660873479370962186721)
        ·
          refine ⟨3595245655109528221640041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793660873479370962186721 3595245655109528221640041)
          ·
            refine ⟨2696434241332146166230031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595245655109528221640041 2696434241332146166230031)
            ·
              refine ⟨4044651361998219249345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696434241332146166230031 4044651361998219249345047)
              ·
                refine ⟨6066977042997328874017571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044651361998219249345047 6066977042997328874017571)
                ·
                  refine ⟨9100465564495993311026357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066977042997328874017571 9100465564495993311026357)
                  ·
                    refine ⟨853168646671499372908721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9100465564495993311026357 853168646671499372908721)
                    ·
                      rfl

theorem cell22_2492310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2492310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492310 prefixEnd_2492310 := by exact prefixLift 2492310
  have htrace : WordTrace (prefixWord ++ tailWord_2492310) baseStart_2492310 baseEnd_2492310 := by
    simpa [prefixWord, tailWord_2492310, baseEnd_2492310] using wordTrace_append hprefix tailTrace_2492310
  have hstable : (prefixWord ++ tailWord_2492310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492310).length < 2 ^ (prefixWord ++ tailWord_2492310).sum := by decide
  have hdescent : baseEnd_2492310 < baseStart_2492310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492381 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2492381 : Nat := 118140960795 + 2492381 * 2 ^ 59
def prefixEnd_2492381 : Nat := 4983230072969 + 3 ^ 40 * 2492381 * 2
def baseEnd_2492381 : Nat := 853192951422478854383503

theorem tailTrace_2492381 : CollatzResearch.WordTrace tailWord_2492381 prefixEnd_2492381 853192951422478854383503 := by
  unfold tailWord_2492381
  simp only [CollatzResearch.WordTrace]
  refine ⟨90904603183536776631004997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60603068789024517754003331 90904603183536776631004997)
  ·
    refine ⟨17044613096913145618313437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90904603183536776631004997 17044613096913145618313437)
    ·
      refine ⟨6391729911342429606867539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17044613096913145618313437 6391729911342429606867539)
      ·
        refine ⟨9587594867013644410301309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391729911342429606867539 9587594867013644410301309)
        ·
          refine ⟨3595348075130116653862991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9587594867013644410301309 3595348075130116653862991)
          ·
            refine ⟨5393022112695174980794487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595348075130116653862991 5393022112695174980794487)
            ·
              refine ⟨8089533169042762471191731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393022112695174980794487 8089533169042762471191731)
              ·
                refine ⟨12134299753564143706787597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089533169042762471191731 12134299753564143706787597)
                ·
                  refine ⟨4550362407586553890045349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12134299753564143706787597 4550362407586553890045349)
                  ·
                    refine ⟨853192951422478854383503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550362407586553890045349 853192951422478854383503)
                    ·
                      rfl

theorem cell22_2492381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2492381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492381 prefixEnd_2492381 := by exact prefixLift 2492381
  have htrace : WordTrace (prefixWord ++ tailWord_2492381) baseStart_2492381 baseEnd_2492381 := by
    simpa [prefixWord, tailWord_2492381, baseEnd_2492381] using wordTrace_append hprefix tailTrace_2492381
  have hstable : (prefixWord ++ tailWord_2492381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492381).length < 2 ^ (prefixWord ++ tailWord_2492381).sum := by decide
  have hdescent : baseEnd_2492381 < baseStart_2492381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492394 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2492394 : Nat := 118140960795 + 2492394 * 2 ^ 59
def prefixEnd_2492394 : Nat := 4983230072969 + 3 ^ 40 * 2492394 * 2
def baseEnd_2492394 : Nat := 853197401588151153808463

theorem tailTrace_2492394 : CollatzResearch.WordTrace tailWord_2492394 prefixEnd_2492394 853197401588151153808463 := by
  unfold tailWord_2492394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726269333122419962807059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60603384888326453234152157 22726269333122419962807059)
  ·
    refine ⟨34089403999683629944210589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726269333122419962807059 34089403999683629944210589)
    ·
      refine ⟨12783526499881361229078971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34089403999683629944210589 12783526499881361229078971)
      ·
        refine ⟨19175289749822041843618457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783526499881361229078971 19175289749822041843618457)
        ·
          refine ⟨14381467312366531382713843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19175289749822041843618457 14381467312366531382713843)
          ·
            refine ⟨21572200968549797074070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14381467312366531382713843 21572200968549797074070765)
            ·
              refine ⟨8089575363206173902776537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21572200968549797074070765 8089575363206173902776537)
              ·
                refine ⟨6067181522404630427082403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089575363206173902776537 6067181522404630427082403)
                ·
                  refine ⟨9100772283606945640623605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067181522404630427082403 9100772283606945640623605)
                  ·
                    refine ⟨853197401588151153808463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9100772283606945640623605 853197401588151153808463)
                    ·
                      rfl

theorem cell22_2492394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2492394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492394 prefixEnd_2492394 := by exact prefixLift 2492394
  have htrace : WordTrace (prefixWord ++ tailWord_2492394) baseStart_2492394 baseEnd_2492394 := by
    simpa [prefixWord, tailWord_2492394, baseEnd_2492394] using wordTrace_append hprefix tailTrace_2492394
  have hstable : (prefixWord ++ tailWord_2492394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492394).length < 2 ^ (prefixWord ++ tailWord_2492394).sum := by decide
  have hdescent : baseEnd_2492394 < baseStart_2492394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492398 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2492398 : Nat := 118140960795 + 2492398 * 2 ^ 59
def prefixEnd_2492398 : Nat := 4983230072969 + 3 ^ 40 * 2492398 * 2
def baseEnd_2492398 : Nat := 853198770869896476708451

theorem tailTrace_2492398 : CollatzResearch.WordTrace tailWord_2492398 prefixEnd_2492398 853198770869896476708451 := by
  unfold tailWord_2492398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363152903059398566796731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60603482149650125689582565 11363152903059398566796731)
  ·
    refine ⟨17044729354589097850195097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11363152903059398566796731 17044729354589097850195097)
    ·
      refine ⟨12783547015941823387646323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17044729354589097850195097 12783547015941823387646323)
      ·
        refine ⟨19175320523912735081469485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783547015941823387646323 19175320523912735081469485)
        ·
          refine ⟨7190745196467275655551057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19175320523912735081469485 7190745196467275655551057)
          ·
            refine ⟨5393058897350456741663293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7190745196467275655551057 5393058897350456741663293)
            ·
              refine ⟨2022397086506421278123735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5393058897350456741663293 2022397086506421278123735)
              ·
                refine ⟨3033595629759631917185603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022397086506421278123735 3033595629759631917185603)
                ·
                  refine ⟨4550393444639447875778405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033595629759631917185603 4550393444639447875778405)
                  ·
                    refine ⟨853198770869896476708451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550393444639447875778405 853198770869896476708451)
                    ·
                      rfl

theorem cell22_2492398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2492398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492398 prefixEnd_2492398 := by exact prefixLift 2492398
  have htrace : WordTrace (prefixWord ++ tailWord_2492398) baseStart_2492398 baseEnd_2492398 := by
    simpa [prefixWord, tailWord_2492398, baseEnd_2492398] using wordTrace_append hprefix tailTrace_2492398
  have hstable : (prefixWord ++ tailWord_2492398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492398).length < 2 ^ (prefixWord ++ tailWord_2492398).sum := by decide
  have hdescent : baseEnd_2492398 < baseStart_2492398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492409 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2492409 : Nat := 118140960795 + 2492409 * 2 ^ 59
def prefixEnd_2492409 : Nat := 4983230072969 + 3 ^ 40 * 2492409 * 2
def baseEnd_2492409 : Nat := 853202536394696114683417

theorem tailTrace_2492409 : CollatzResearch.WordTrace tailWord_2492409 prefixEnd_2492409 853202536394696114683417 := by
  unfold tailWord_2492409
  simp only [CollatzResearch.WordTrace]
  refine ⟨90905624427435337413024281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60603749618290224942016187 90905624427435337413024281)
  ·
    refine ⟨68179218320576503059768211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90905624427435337413024281 68179218320576503059768211)
    ·
      refine ⟨102268827480864754589652317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68179218320576503059768211 102268827480864754589652317)
      ·
        refine ⟨38350810305324282971119619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102268827480864754589652317 38350810305324282971119619)
        ·
          refine ⟨57526215457986424456679429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38350810305324282971119619 57526215457986424456679429)
          ·
            refine ⟨10786165398372454585627393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57526215457986424456679429 10786165398372454585627393)
            ·
              refine ⟨8089624048779340939220545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786165398372454585627393 8089624048779340939220545)
              ·
                refine ⟨6067218036584505704415409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089624048779340939220545 6067218036584505704415409)
                ·
                  refine ⟨4550413527438379278311557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067218036584505704415409 4550413527438379278311557)
                  ·
                    refine ⟨853202536394696114683417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550413527438379278311557 853202536394696114683417)
                    ·
                      rfl

theorem cell22_2492409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2492409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492409 prefixEnd_2492409 := by exact prefixLift 2492409
  have htrace : WordTrace (prefixWord ++ tailWord_2492409) baseStart_2492409 baseEnd_2492409 := by
    simpa [prefixWord, tailWord_2492409, baseEnd_2492409] using wordTrace_append hprefix tailTrace_2492409
  have hstable : (prefixWord ++ tailWord_2492409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492409).length < 2 ^ (prefixWord ++ tailWord_2492409).sum := by decide
  have hdescent : baseEnd_2492409 < baseStart_2492409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492473 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_2492473 : Nat := 118140960795 + 2492473 * 2 ^ 59
def prefixEnd_2492473 : Nat := 4983230072969 + 3 ^ 40 * 2492473 * 2
def baseEnd_2492473 : Nat := 853224444902621281083221

theorem tailTrace_2492473 : CollatzResearch.WordTrace tailWord_2492473 prefixEnd_2492473 853224444902621281083221 := by
  unfold tailWord_2492473
  simp only [CollatzResearch.WordTrace]
  refine ⟨90907958699203476343354073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60605305799468984228902715 90907958699203476343354073)
  ·
    refine ⟨68180969024402607257515555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90907958699203476343354073 68180969024402607257515555)
    ·
      refine ⟨102271453536603910886273333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68180969024402607257515555 102271453536603910886273333)
      ·
        refine ⟨9587948769056616645588125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102271453536603910886273333 9587948769056616645588125)
        ·
          refine ⟨3595480788396231242095547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9587948769056616645588125 3595480788396231242095547)
          ·
            refine ⟨5393221182594346863143321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595480788396231242095547 5393221182594346863143321)
            ·
              refine ⟨4044915886945760147357491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393221182594346863143321 4044915886945760147357491)
              ·
                refine ⟨6067373830418640221036237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044915886945760147357491 6067373830418640221036237)
                ·
                  refine ⟨2275265186406990082888589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6067373830418640221036237 2275265186406990082888589)
                  ·
                    refine ⟨853224444902621281083221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275265186406990082888589 853224444902621281083221)
                    ·
                      rfl

theorem cell22_2492473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_2492473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492473 prefixEnd_2492473 := by exact prefixLift 2492473
  have htrace : WordTrace (prefixWord ++ tailWord_2492473) baseStart_2492473 baseEnd_2492473 := by
    simpa [prefixWord, tailWord_2492473, baseEnd_2492473] using wordTrace_append hprefix tailTrace_2492473
  have hstable : (prefixWord ++ tailWord_2492473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492473).length < 2 ^ (prefixWord ++ tailWord_2492473).sum := by decide
  have hdescent : baseEnd_2492473 < baseStart_2492473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492516 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2492516 : Nat := 118140960795 + 2492516 * 2 ^ 59
def prefixEnd_2492516 : Nat := 4983230072969 + 3 ^ 40 * 2492516 * 2
def baseEnd_2492516 : Nat := 853239164681383502258089

theorem tailTrace_2492516 : CollatzResearch.WordTrace tailWord_2492516 prefixEnd_2492516 853239164681383502258089 := by
  unfold tailWord_2492516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45454763519023847343584701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60606351358698463124779601 45454763519023847343584701)
  ·
    refine ⟨17045536319633942753844263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45454763519023847343584701 17045536319633942753844263)
    ·
      refine ⟨25568304479450914130766395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17045536319633942753844263 25568304479450914130766395)
      ·
        refine ⟨38352456719176371196149593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568304479450914130766395 38352456719176371196149593)
        ·
          refine ⟨28764342539382278397112195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38352456719176371196149593 28764342539382278397112195)
          ·
            refine ⟨43146513809073417595668293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28764342539382278397112195 43146513809073417595668293)
            ·
              refine ⟨8089971339201265799187805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43146513809073417595668293 8089971339201265799187805)
              ·
                refine ⟨3033739252200474674695427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8089971339201265799187805 3033739252200474674695427)
                ·
                  refine ⟨4550608878300712012043141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033739252200474674695427 4550608878300712012043141)
                  ·
                    refine ⟨853239164681383502258089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550608878300712012043141 853239164681383502258089)
                    ·
                      rfl

theorem cell22_2492516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2492516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492516 prefixEnd_2492516 := by exact prefixLift 2492516
  have htrace : WordTrace (prefixWord ++ tailWord_2492516) baseStart_2492516 baseEnd_2492516 := by
    simpa [prefixWord, tailWord_2492516, baseEnd_2492516] using wordTrace_append hprefix tailTrace_2492516
  have hstable : (prefixWord ++ tailWord_2492516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492516).length < 2 ^ (prefixWord ++ tailWord_2492516).sum := by decide
  have hdescent : baseEnd_2492516 < baseStart_2492516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_2492544 : Nat := 118140960795 + 2492544 * 2 ^ 59
def prefixEnd_2492544 : Nat := 4983230072969 + 3 ^ 40 * 2492544 * 2
def baseEnd_2492544 : Nat := 853248749653600762558003

theorem tailTrace_2492544 : CollatzResearch.WordTrace tailWord_2492544 prefixEnd_2492544 853248749653600762558003 := by
  unfold tailWord_2492544
  simp only [CollatzResearch.WordTrace]
  refine ⟨45455274140973127734594343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60607032187964170312792457 45455274140973127734594343)
  ·
    refine ⟨68182911211459691601891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45455274140973127734594343 68182911211459691601891515)
    ·
      refine ⟨102274366817189537402837273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68182911211459691601891515 102274366817189537402837273)
      ·
        refine ⟨76705775112892153052127955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102274366817189537402837273 76705775112892153052127955)
        ·
          refine ⟨115058662669338229578191933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76705775112892153052127955 115058662669338229578191933)
          ·
            refine ⟨43146998501001836091821975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115058662669338229578191933 43146998501001836091821975)
            ·
              refine ⟨64720497751502754137732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43146998501001836091821975 64720497751502754137732963)
              ·
                refine ⟨97080746627254131206599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64720497751502754137732963 97080746627254131206599445)
                ·
                  refine ⟨4550659998152537400309349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97080746627254131206599445 4550659998152537400309349)
                  ·
                    refine ⟨853248749653600762558003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550659998152537400309349 853248749653600762558003)
                    ·
                      rfl

theorem cell22_2492544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_2492544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492544 prefixEnd_2492544 := by exact prefixLift 2492544
  have htrace : WordTrace (prefixWord ++ tailWord_2492544) baseStart_2492544 baseEnd_2492544 := by
    simpa [prefixWord, tailWord_2492544, baseEnd_2492544] using wordTrace_append hprefix tailTrace_2492544
  have hstable : (prefixWord ++ tailWord_2492544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492544).length < 2 ^ (prefixWord ++ tailWord_2492544).sum := by decide
  have hdescent : baseEnd_2492544 < baseStart_2492544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492578 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2492578 : Nat := 118140960795 + 2492578 * 2 ^ 59
def prefixEnd_2492578 : Nat := 4983230072969 + 3 ^ 40 * 2492578 * 2
def baseEnd_2492578 : Nat := 853260388548436007207899

theorem tailTrace_2492578 : CollatzResearch.WordTrace tailWord_2492578 prefixEnd_2492578 853260388548436007207899 := by
  unfold tailWord_2492578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727947090955769818981597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60607858909215386183950925 22727947090955769818981597)
  ·
    refine ⟨8522980159108413682118099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22727947090955769818981597 8522980159108413682118099)
    ·
      refine ⟨12784470238662620523177149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522980159108413682118099 12784470238662620523177149)
      ·
        refine ⟨4794176339498482696191431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12784470238662620523177149 4794176339498482696191431)
        ·
          refine ⟨7191264509247724044287147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4794176339498482696191431 7191264509247724044287147)
          ·
            refine ⟨10786896763871586066430721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191264509247724044287147 10786896763871586066430721)
            ·
              refine ⟨8090172572903689549823041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786896763871586066430721 8090172572903689549823041)
              ·
                refine ⟨6067629429677767162367281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090172572903689549823041 6067629429677767162367281)
                ·
                  refine ⟨4550722072258325371775461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067629429677767162367281 4550722072258325371775461)
                  ·
                    refine ⟨853260388548436007207899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550722072258325371775461 853260388548436007207899)
                    ·
                      rfl

theorem cell22_2492578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2492578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492578 prefixEnd_2492578 := by exact prefixLift 2492578
  have htrace : WordTrace (prefixWord ++ tailWord_2492578) baseStart_2492578 baseEnd_2492578 := by
    simpa [prefixWord, tailWord_2492578, baseEnd_2492578] using wordTrace_append hprefix tailTrace_2492578
  have hstable : (prefixWord ++ tailWord_2492578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492578).length < 2 ^ (prefixWord ++ tailWord_2492578).sum := by decide
  have hdescent : baseEnd_2492578 < baseStart_2492578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492580 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2492580 : Nat := 118140960795 + 2492580 * 2 ^ 59
def prefixEnd_2492580 : Nat := 4983230072969 + 3 ^ 40 * 2492580 * 2
def baseEnd_2492580 : Nat := 853261073189308668657893

theorem tailTrace_2492580 : CollatzResearch.WordTrace tailWord_2492580 prefixEnd_2492580 853261073189308668657893 := by
  unfold tailWord_2492580
  simp only [CollatzResearch.WordTrace]
  refine ⟨45455930654907916808749597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60607907539877222411666129 45455930654907916808749597)
  ·
    refine ⟨17045973995590468803281099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45455930654907916808749597 17045973995590468803281099)
    ·
      refine ⟨25568960993385703204921649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17045973995590468803281099 25568960993385703204921649)
      ·
        refine ⟨19176720745039277403691237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25568960993385703204921649 19176720745039277403691237)
        ·
          refine ⟨3595635139694864513192107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19176720745039277403691237 3595635139694864513192107)
          ·
            refine ⟨5393452709542296769788161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595635139694864513192107 5393452709542296769788161)
            ·
              refine ⟨4045089532156722577341121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393452709542296769788161 4045089532156722577341121)
              ·
                refine ⟨3033817149117541933005841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045089532156722577341121 3033817149117541933005841)
                ·
                  refine ⟨2275362861838156449754381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3033817149117541933005841 2275362861838156449754381)
                  ·
                    refine ⟨853261073189308668657893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275362861838156449754381 853261073189308668657893)
                    ·
                      rfl

theorem cell22_2492580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2492580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492580 prefixEnd_2492580 := by exact prefixLift 2492580
  have htrace : WordTrace (prefixWord ++ tailWord_2492580) baseStart_2492580 baseEnd_2492580 := by
    simpa [prefixWord, tailWord_2492580, baseEnd_2492580] using wordTrace_append hprefix tailTrace_2492580
  have hstable : (prefixWord ++ tailWord_2492580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492580).length < 2 ^ (prefixWord ++ tailWord_2492580).sum := by decide
  have hdescent : baseEnd_2492580 < baseStart_2492580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492591 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 3, 3]
def baseStart_2492591 : Nat := 118140960795 + 2492591 * 2 ^ 59
def prefixEnd_2492591 : Nat := 4983230072969 + 3 ^ 40 * 2492591 * 2
def baseEnd_2492591 : Nat := 853264838714108306632859

theorem tailTrace_2492591 : CollatzResearch.WordTrace tailWord_2492591 prefixEnd_2492591 853264838714108306632859 := by
  unfold tailWord_2492591
  simp only [CollatzResearch.WordTrace]
  refine ⟨90912262512775982496149627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60608175008517321664099751 90912262512775982496149627)
  ·
    refine ⟨136368393769163973744224441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90912262512775982496149627 136368393769163973744224441)
    ·
      refine ⟨102276295326872980308168331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136368393769163973744224441 102276295326872980308168331)
      ·
        refine ⟨153414442990309470462252497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102276295326872980308168331 153414442990309470462252497)
        ·
          refine ⟨115060832242732102846689373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153414442990309470462252497 115060832242732102846689373)
          ·
            refine ⟨43147812091024538567508515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115060832242732102846689373 43147812091024538567508515)
            ·
              refine ⟨64721718136536807851262773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43147812091024538567508515 64721718136536807851262773)
              ·
                refine ⟨6067661075300325736055885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64721718136536807851262773 6067661075300325736055885)
                ·
                  refine ⟨2275372903237622151020957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6067661075300325736055885 2275372903237622151020957)
                  ·
                    refine ⟨853264838714108306632859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275372903237622151020957 853264838714108306632859)
                    ·
                      rfl

theorem cell22_2492591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_2492591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492591 prefixEnd_2492591 := by exact prefixLift 2492591
  have htrace : WordTrace (prefixWord ++ tailWord_2492591) baseStart_2492591 baseEnd_2492591 := by
    simpa [prefixWord, tailWord_2492591, baseEnd_2492591] using wordTrace_append hprefix tailTrace_2492591
  have hstable : (prefixWord ++ tailWord_2492591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492591).length < 2 ^ (prefixWord ++ tailWord_2492591).sum := by decide
  have hdescent : baseEnd_2492591 < baseStart_2492591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492593 : List Nat := [1, 2, 2, 5, 2, 2, 1, 7]
def baseStart_2492593 : Nat := 118140960795 + 2492593 * 2 ^ 59
def prefixEnd_2492593 : Nat := 4983230072969 + 3 ^ 40 * 2492593 * 2
def baseEnd_2492593 : Nat := 94807280372775663120317

theorem tailTrace_2492593 : CollatzResearch.WordTrace tailWord_2492593 prefixEnd_2492593 94807280372775663120317 := by
  unfold tailWord_2492593
  simp only [CollatzResearch.WordTrace]
  refine ⟨90912335458768736837722433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60608223639179157891814955 90912335458768736837722433)
  ·
    refine ⟨68184251594076552628291825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90912335458768736837722433 68184251594076552628291825)
    ·
      refine ⟨51138188695557414471218869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68184251594076552628291825 51138188695557414471218869)
      ·
        refine ⟨4794205190208507606676769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51138188695557414471218869 4794205190208507606676769)
        ·
          refine ⟨3595653892656380705007577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794205190208507606676769 3595653892656380705007577)
          ·
            refine ⟨2696740419492285528755683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595653892656380705007577 2696740419492285528755683)
            ·
              refine ⟨4045110629238428293133525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696740419492285528755683 4045110629238428293133525)
              ·
                refine ⟨94807280372775663120317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4045110629238428293133525 94807280372775663120317)
                ·
                  rfl

theorem cell22_2492593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 7].length) (baseStart_2492593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492593 prefixEnd_2492593 := by exact prefixLift 2492593
  have htrace : WordTrace (prefixWord ++ tailWord_2492593) baseStart_2492593 baseEnd_2492593 := by
    simpa [prefixWord, tailWord_2492593, baseEnd_2492593] using wordTrace_append hprefix tailTrace_2492593
  have hstable : (prefixWord ++ tailWord_2492593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492593).length < 2 ^ (prefixWord ++ tailWord_2492593).sum := by decide
  have hdescent : baseEnd_2492593 < baseStart_2492593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492608 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_2492608 : Nat := 118140960795 + 2492608 * 2 ^ 59
def prefixEnd_2492608 : Nat := 4983230072969 + 3 ^ 40 * 2492608 * 2
def baseEnd_2492608 : Nat := 853270658161525928957807

theorem tailTrace_2492608 : CollatzResearch.WordTrace tailWord_2492608 prefixEnd_2492608 853270658161525928957807 := by
  unfold tailWord_2492608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45456441276857197199759239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60608588369142929599678985 45456441276857197199759239)
  ·
    refine ⟨68184661915285795799638859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45456441276857197199759239 68184661915285795799638859)
    ·
      refine ⟨102276992872928693699458289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68184661915285795799638859 102276992872928693699458289)
      ·
        refine ⟨76707744654696520274593717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102276992872928693699458289 76707744654696520274593717)
        ·
          refine ⟨7191351061377798775743161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76707744654696520274593717 7191351061377798775743161)
          ·
            refine ⟨5393513296033349081807371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7191351061377798775743161 5393513296033349081807371)
            ·
              refine ⟨8090269944050023622711057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393513296033349081807371 8090269944050023622711057)
              ·
                refine ⟨6067702458037517717033293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090269944050023622711057 6067702458037517717033293)
                ·
                  refine ⟨2275388421764069143887485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6067702458037517717033293 2275388421764069143887485)
                  ·
                    refine ⟨853270658161525928957807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275388421764069143887485 853270658161525928957807)
                    ·
                      rfl

theorem cell22_2492608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_2492608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492608 prefixEnd_2492608 := by exact prefixLift 2492608
  have htrace : WordTrace (prefixWord ++ tailWord_2492608) baseStart_2492608 baseEnd_2492608 := by
    simpa [prefixWord, tailWord_2492608, baseEnd_2492608] using wordTrace_append hprefix tailTrace_2492608
  have hstable : (prefixWord ++ tailWord_2492608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492608).length < 2 ^ (prefixWord ++ tailWord_2492608).sum := by decide
  have hdescent : baseEnd_2492608 < baseStart_2492608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492619 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_2492619 : Nat := 118140960795 + 2492619 * 2 ^ 59
def prefixEnd_2492619 : Nat := 4983230072969 + 3 ^ 40 * 2492619 * 2
def baseEnd_2492619 : Nat := 853274423686325566932773

theorem tailTrace_2492619 : CollatzResearch.WordTrace tailWord_2492619 prefixEnd_2492619 853274423686325566932773 := by
  unfold tailWord_2492619
  simp only [CollatzResearch.WordTrace]
  refine ⟨90913283756674543278168911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60608855837783028852112607 90913283756674543278168911)
  ·
    refine ⟨136369925635011814917253367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90913283756674543278168911 136369925635011814917253367)
    ·
      refine ⟨204554888452517722375880051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136369925635011814917253367 204554888452517722375880051)
      ·
        refine ⟨306832332678776583563820077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204554888452517722375880051 306832332678776583563820077)
        ·
          refine ⟨115062124754541218836432529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306832332678776583563820077 115062124754541218836432529)
          ·
            refine ⟨86296593565905914127324397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115062124754541218836432529 86296593565905914127324397)
            ·
              refine ⟨32361222587214717797746649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86296593565905914127324397 32361222587214717797746649)
              ·
                refine ⟨24270916940411038348309987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32361222587214717797746649 24270916940411038348309987)
                ·
                  refine ⟨36406375410616557522464981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24270916940411038348309987 36406375410616557522464981)
                  ·
                    refine ⟨853274423686325566932773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36406375410616557522464981 853274423686325566932773)
                    ·
                      rfl

theorem cell22_2492619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_2492619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492619 prefixEnd_2492619 := by exact prefixLift 2492619
  have htrace : WordTrace (prefixWord ++ tailWord_2492619) baseStart_2492619 baseEnd_2492619 := by
    simpa [prefixWord, tailWord_2492619, baseEnd_2492619] using wordTrace_append hprefix tailTrace_2492619
  have hstable : (prefixWord ++ tailWord_2492619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492619).length < 2 ^ (prefixWord ++ tailWord_2492619).sum := by decide
  have hdescent : baseEnd_2492619 < baseStart_2492619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492649 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 10]
def baseStart_2492649 : Nat := 118140960795 + 2492649 * 2 ^ 59
def prefixEnd_2492649 : Nat := 4983230072969 + 3 ^ 40 * 2492649 * 2
def baseEnd_2492649 : Nat := 284428231099805162894227

theorem tailTrace_2492649 : CollatzResearch.WordTrace tailWord_2492649 prefixEnd_2492649 284428231099805162894227 := by
  unfold tailWord_2492649
  simp only [CollatzResearch.WordTrace]
  refine ⟨90914377946565858401761001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60609585297710572267840667 90914377946565858401761001)
  ·
    refine ⟨68185783459924393801320751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90914377946565858401761001 68185783459924393801320751)
    ·
      refine ⟨102278675189886590701981127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68185783459924393801320751 102278675189886590701981127)
      ·
        refine ⟨153418012784829886052971691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102278675189886590701981127 153418012784829886052971691)
        ·
          refine ⟨230127019177244829079457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153418012784829886052971691 230127019177244829079457537)
          ·
            refine ⟨172595264382933621809593153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230127019177244829079457537 172595264382933621809593153)
            ·
              refine ⟨129446448287200216357194865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172595264382933621809593153 129446448287200216357194865)
              ·
                refine ⟨97084836215400162267896149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129446448287200216357194865 97084836215400162267896149)
                ·
                  refine ⟨284428231099805162894227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97084836215400162267896149 284428231099805162894227)
                  ·
                    rfl

theorem cell22_2492649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_2492649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492649 prefixEnd_2492649 := by exact prefixLift 2492649
  have htrace : WordTrace (prefixWord ++ tailWord_2492649) baseStart_2492649 baseEnd_2492649 := by
    simpa [prefixWord, tailWord_2492649, baseEnd_2492649] using wordTrace_append hprefix tailTrace_2492649
  have hstable : (prefixWord ++ tailWord_2492649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492649).length < 2 ^ (prefixWord ++ tailWord_2492649).sum := by decide
  have hdescent : baseEnd_2492649 < baseStart_2492649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492666 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_2492666 : Nat := 118140960795 + 2492666 * 2 ^ 59
def prefixEnd_2492666 : Nat := 4983230072969 + 3 ^ 40 * 2492666 * 2
def baseEnd_2492666 : Nat := 284430170915611037002543

theorem tailTrace_2492666 : CollatzResearch.WordTrace tailWord_2492666 prefixEnd_2492666 284430170915611037002543 := by
  unfold tailWord_2492666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728749496876067576282463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60609998658336180203419901 22728749496876067576282463)
  ·
    refine ⟨34093124245314101364423695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22728749496876067576282463 34093124245314101364423695)
    ·
      refine ⟨51139686367971152046635543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34093124245314101364423695 51139686367971152046635543)
      ·
        refine ⟨76709529551956728069953315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51139686367971152046635543 76709529551956728069953315)
        ·
          refine ⟨115064294327935092104929973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76709529551956728069953315 115064294327935092104929973)
          ·
            refine ⟨10787277593243914884837185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115064294327935092104929973 10787277593243914884837185)
            ·
              refine ⟨8090458194932936163627889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10787277593243914884837185 8090458194932936163627889)
              ·
                refine ⟨6067843646199702122720917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090458194932936163627889 6067843646199702122720917)
                ·
                  refine ⟨284430170915611037002543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6067843646199702122720917 284430170915611037002543)
                  ·
                    rfl

theorem cell22_2492666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_2492666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492666 prefixEnd_2492666 := by exact prefixLift 2492666
  have htrace : WordTrace (prefixWord ++ tailWord_2492666) baseStart_2492666 baseEnd_2492666 := by
    simpa [prefixWord, tailWord_2492666, baseEnd_2492666] using wordTrace_append hprefix tailTrace_2492666
  have hstable : (prefixWord ++ tailWord_2492666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492666).length < 2 ^ (prefixWord ++ tailWord_2492666).sum := by decide
  have hdescent : baseEnd_2492666 < baseStart_2492666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492668 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2492668 : Nat := 118140960795 + 2492668 * 2 ^ 59
def prefixEnd_2492668 : Nat := 4983230072969 + 3 ^ 40 * 2492668 * 2
def baseEnd_2492668 : Nat := 853291197387705772457623

theorem tailTrace_2492668 : CollatzResearch.WordTrace tailWord_2492668 prefixEnd_2492668 853291197387705772457623 := by
  unfold tailWord_2492668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45457535466748512323351329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60610047288998016431135105 45457535466748512323351329)
  ·
    refine ⟨34093151600061384242513497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45457535466748512323351329 34093151600061384242513497)
    ·
      refine ⟨25569863700046038181885123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34093151600061384242513497 25569863700046038181885123)
      ·
        refine ⟨38354795550069057272827685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25569863700046038181885123 38354795550069057272827685)
        ·
          refine ⟨7191524165637948238655191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38354795550069057272827685 7191524165637948238655191)
          ·
            refine ⟨10787286248456922357982787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191524165637948238655191 10787286248456922357982787)
            ·
              refine ⟨16180929372685383536974181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10787286248456922357982787 16180929372685383536974181)
              ·
                refine ⟨3033924257378509413182659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16180929372685383536974181 3033924257378509413182659)
                ·
                  refine ⟨4550886386067764119773989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033924257378509413182659 4550886386067764119773989)
                  ·
                    refine ⟨853291197387705772457623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550886386067764119773989 853291197387705772457623)
                    ·
                      rfl

theorem cell22_2492668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2492668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492668 prefixEnd_2492668 := by exact prefixLift 2492668
  have htrace : WordTrace (prefixWord ++ tailWord_2492668) baseStart_2492668 baseEnd_2492668 := by
    simpa [prefixWord, tailWord_2492668, baseEnd_2492668] using wordTrace_append hprefix tailTrace_2492668
  have hstable : (prefixWord ++ tailWord_2492668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492668).length < 2 ^ (prefixWord ++ tailWord_2492668).sum := by decide
  have hdescent : baseEnd_2492668 < baseStart_2492668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492766 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2492766 : Nat := 118140960795 + 2492766 * 2 ^ 59
def prefixEnd_2492766 : Nat := 4983230072969 + 3 ^ 40 * 2492766 * 2
def baseEnd_2492766 : Nat := 853324744790466183507323

theorem tailTrace_2492766 : CollatzResearch.WordTrace tailWord_2492766 prefixEnd_2492766 853324744790466183507323 := by
  unfold tailWord_2492766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364830660892748422971269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60612430191427991589180101 11364830660892748422971269)
  ·
    refine ⟨2130905748917390329307113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11364830660892748422971269 2130905748917390329307113)
    ·
      refine ⟨1598179311688042746980335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2130905748917390329307113 1598179311688042746980335)
      ·
        refine ⟨2397268967532064120470503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598179311688042746980335 2397268967532064120470503)
        ·
          refine ⟨3595903451298096180705755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397268967532064120470503 3595903451298096180705755)
          ·
            refine ⟨5393855176947144271058633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595903451298096180705755 5393855176947144271058633)
            ·
              refine ⟨4045391382710358203293975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393855176947144271058633 4045391382710358203293975)
              ·
                refine ⟨6068087074065537304940963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045391382710358203293975 6068087074065537304940963)
                ·
                  refine ⟨9102130611098305957411445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068087074065537304940963 9102130611098305957411445)
                  ·
                    refine ⟨853324744790466183507323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9102130611098305957411445 853324744790466183507323)
                    ·
                      rfl

theorem cell22_2492766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2492766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492766 prefixEnd_2492766 := by exact prefixLift 2492766
  have htrace : WordTrace (prefixWord ++ tailWord_2492766) baseStart_2492766 baseEnd_2492766 := by
    simpa [prefixWord, tailWord_2492766, baseEnd_2492766] using wordTrace_append hprefix tailTrace_2492766
  have hstable : (prefixWord ++ tailWord_2492766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492766).length < 2 ^ (prefixWord ++ tailWord_2492766).sum := by decide
  have hdescent : baseEnd_2492766 < baseStart_2492766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492773 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 5]
def baseStart_2492773 : Nat := 118140960795 + 2492773 * 2 ^ 59
def prefixEnd_2492773 : Nat := 4983230072969 + 3 ^ 40 * 2492773 * 2
def baseEnd_2492773 : Nat := 284442380344506832860767

theorem tailTrace_2492773 : CollatzResearch.WordTrace tailWord_2492773 prefixEnd_2492773 284442380344506832860767 := by
  unfold tailWord_2492773
  simp only [CollatzResearch.WordTrace]
  refine ⟨90918900598116627579274973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60612600398744418386183315 90918900598116627579274973)
  ·
    refine ⟨34094587724293735342228115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90918900598116627579274973 34094587724293735342228115)
    ·
      refine ⟨51141881586440603013342173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34094587724293735342228115 51141881586440603013342173)
      ·
        refine ⟨19178205594915226130003315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51141881586440603013342173 19178205594915226130003315)
        ·
          refine ⟨28767308392372839195004973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19178205594915226130003315 28767308392372839195004973)
          ·
            refine ⟨10787740647139814698126865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28767308392372839195004973 10787740647139814698126865)
            ·
              refine ⟨8090805485354861023595149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10787740647139814698126865 8090805485354861023595149)
              ·
                refine ⟨3034052057008072883848181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8090805485354861023595149 3034052057008072883848181)
                ·
                  refine ⟨284442380344506832860767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3034052057008072883848181 284442380344506832860767)
                  ·
                    rfl

theorem cell22_2492773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_2492773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492773 prefixEnd_2492773 := by exact prefixLift 2492773
  have htrace : WordTrace (prefixWord ++ tailWord_2492773) baseStart_2492773 baseEnd_2492773 := by
    simpa [prefixWord, tailWord_2492773, baseEnd_2492773] using wordTrace_append hprefix tailTrace_2492773
  have hstable : (prefixWord ++ tailWord_2492773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492773).length < 2 ^ (prefixWord ++ tailWord_2492773).sum := by decide
  have hdescent : baseEnd_2492773 < baseStart_2492773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492884 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2492884 : Nat := 118140960795 + 2492884 * 2 ^ 59
def prefixEnd_2492884 : Nat := 4983230072969 + 3 ^ 40 * 2492884 * 2
def baseEnd_2492884 : Nat := 853365138601953209056961

theorem tailTrace_2492884 : CollatzResearch.WordTrace tailWord_2492884 prefixEnd_2492884 853365138601953209056961 := by
  unfold tailWord_2492884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45461474550357246768282853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60615299400476329024377137 45461474550357246768282853)
  ·
    refine ⟨8524026478191983769053035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45461474550357246768282853 8524026478191983769053035)
    ·
      refine ⟨12786039717287975653579553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8524026478191983769053035 12786039717287975653579553)
      ·
        refine ⟨9589529787965981740184665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12786039717287975653579553 9589529787965981740184665)
        ·
          refine ⟨7192147340974486305138499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9589529787965981740184665 7192147340974486305138499)
          ·
            refine ⟨10788221011461729457707749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192147340974486305138499 10788221011461729457707749)
            ·
              refine ⟨2022791439649074273320203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10788221011461729457707749 2022791439649074273320203)
              ·
                refine ⟨3034187159473611409980305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022791439649074273320203 3034187159473611409980305)
                ·
                  refine ⟨2275640369605208557485229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034187159473611409980305 2275640369605208557485229)
                  ·
                    refine ⟨853365138601953209056961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275640369605208557485229 853365138601953209056961)
                    ·
                      rfl

theorem cell22_2492884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2492884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492884 prefixEnd_2492884 := by exact prefixLift 2492884
  have htrace : WordTrace (prefixWord ++ tailWord_2492884) baseStart_2492884 baseEnd_2492884 := by
    simpa [prefixWord, tailWord_2492884, baseEnd_2492884] using wordTrace_append hprefix tailTrace_2492884
  have hstable : (prefixWord ++ tailWord_2492884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492884).length < 2 ^ (prefixWord ++ tailWord_2492884).sum := by decide
  have hdescent : baseEnd_2492884 < baseStart_2492884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492912 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_2492912 : Nat := 118140960795 + 2492912 * 2 ^ 59
def prefixEnd_2492912 : Nat := 4983230072969 + 3 ^ 40 * 2492912 * 2
def baseEnd_2492912 : Nat := 853374723574170469356875

theorem tailTrace_2492912 : CollatzResearch.WordTrace tailWord_2492912 prefixEnd_2492912 853374723574170469356875 := by
  unfold tailWord_2492912
  simp only [CollatzResearch.WordTrace]
  refine ⟨45461985172306527159292495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60615980229742036212389993 45461985172306527159292495)
  ·
    refine ⟨68192977758459790738938743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45461985172306527159292495 68192977758459790738938743)
    ·
      refine ⟨102289466637689686108408115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68192977758459790738938743 102289466637689686108408115)
      ·
        refine ⟨153434199956534529162612173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102289466637689686108408115 153434199956534529162612173)
        ·
          refine ⟨57537824983700448435979565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153434199956534529162612173 57537824983700448435979565)
          ·
            refine ⟨21576684368887668163492337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57537824983700448435979565 21576684368887668163492337)
            ·
              refine ⟨16182513276665751122619253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21576684368887668163492337 16182513276665751122619253)
              ·
                refine ⟨1517110619687414167745555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16182513276665751122619253 1517110619687414167745555)
                ·
                  refine ⟨2275665929531121251618333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517110619687414167745555 2275665929531121251618333)
                  ·
                    refine ⟨853374723574170469356875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275665929531121251618333 853374723574170469356875)
                    ·
                      rfl

theorem cell22_2492912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_2492912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492912 prefixEnd_2492912 := by exact prefixLift 2492912
  have htrace : WordTrace (prefixWord ++ tailWord_2492912) baseStart_2492912 baseEnd_2492912 := by
    simpa [prefixWord, tailWord_2492912, baseEnd_2492912] using wordTrace_append hprefix tailTrace_2492912
  have hstable : (prefixWord ++ tailWord_2492912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492912).length < 2 ^ (prefixWord ++ tailWord_2492912).sum := by decide
  have hdescent : baseEnd_2492912 < baseStart_2492912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492925 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2492925 : Nat := 118140960795 + 2492925 * 2 ^ 59
def prefixEnd_2492925 : Nat := 4983230072969 + 3 ^ 40 * 2492925 * 2
def baseEnd_2492925 : Nat := 284459724579947589593945

theorem tailTrace_2492925 : CollatzResearch.WordTrace tailWord_2492925 prefixEnd_2492925 284459724579947589593945 := by
  unfold tailWord_2492925
  simp only [CollatzResearch.WordTrace]
  refine ⟨90924444493565957538808229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60616296329043971692538819 90924444493565957538808229)
  ·
    refine ⟨17048333342543617038526543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90924444493565957538808229 17048333342543617038526543)
    ·
      refine ⟨25572500013815425557789815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17048333342543617038526543 25572500013815425557789815)
      ·
        refine ⟨38358750020723138336684723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572500013815425557789815 38358750020723138336684723)
        ·
          refine ⟨57538125031084707505027085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38358750020723138336684723 57538125031084707505027085)
          ·
            refine ⟨21576796886656765314385157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57538125031084707505027085 21576796886656765314385157)
            ·
              refine ⟨4045649416248143496447217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21576796886656765314385157 4045649416248143496447217)
              ·
                refine ⟨3034237062186107622335413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045649416248143496447217 3034237062186107622335413)
                ·
                  refine ⟨284459724579947589593945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3034237062186107622335413 284459724579947589593945)
                  ·
                    rfl

theorem cell22_2492925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2492925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492925 prefixEnd_2492925 := by exact prefixLift 2492925
  have htrace : WordTrace (prefixWord ++ tailWord_2492925) baseStart_2492925 baseEnd_2492925 := by
    simpa [prefixWord, tailWord_2492925, baseEnd_2492925] using wordTrace_append hprefix tailTrace_2492925
  have hstable : (prefixWord ++ tailWord_2492925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492925).length < 2 ^ (prefixWord ++ tailWord_2492925).sum := by decide
  have hdescent : baseEnd_2492925 < baseStart_2492925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492929 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2492929 : Nat := 118140960795 + 2492929 * 2 ^ 59
def prefixEnd_2492929 : Nat := 4983230072969 + 3 ^ 40 * 2492929 * 2
def baseEnd_2492929 : Nat := 853380543021588091681823

theorem tailTrace_2492929 : CollatzResearch.WordTrace tailWord_2492929 prefixEnd_2492929 853380543021588091681823 := by
  unfold tailWord_2492929
  simp only [CollatzResearch.WordTrace]
  refine ⟨90924590385551466221953841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60616393590367644147969227 90924590385551466221953841)
  ·
    refine ⟨68193442789163599666465381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90924590385551466221953841 68193442789163599666465381)
    ·
      refine ⟨12786270522968174937462259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68193442789163599666465381 12786270522968174937462259)
      ·
        refine ⟨19179405784452262406193389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12786270522968174937462259 19179405784452262406193389)
        ·
          refine ⟨7192277169169598402322521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19179405784452262406193389 7192277169169598402322521)
          ·
            refine ⟨5394207876877198801741891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7192277169169598402322521 5394207876877198801741891)
            ·
              refine ⟨8091311815315798202612837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394207876877198801741891 8091311815315798202612837)
              ·
                refine ⟨1517120965371712162989907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8091311815315798202612837 1517120965371712162989907)
                ·
                  refine ⟨2275681448057568244484861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517120965371712162989907 2275681448057568244484861)
                  ·
                    refine ⟨853380543021588091681823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275681448057568244484861 853380543021588091681823)
                    ·
                      rfl

theorem cell22_2492929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2492929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492929 prefixEnd_2492929 := by exact prefixLift 2492929
  have htrace : WordTrace (prefixWord ++ tailWord_2492929) baseStart_2492929 baseEnd_2492929 := by
    simpa [prefixWord, tailWord_2492929, baseEnd_2492929] using wordTrace_append hprefix tailTrace_2492929
  have hstable : (prefixWord ++ tailWord_2492929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492929).length < 2 ^ (prefixWord ++ tailWord_2492929).sum := by decide
  have hdescent : baseEnd_2492929 < baseStart_2492929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492940 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2492940 : Nat := 118140960795 + 2492940 * 2 ^ 59
def prefixEnd_2492940 : Nat := 4983230072969 + 3 ^ 40 * 2492940 * 2
def baseEnd_2492940 : Nat := 853384308546387729656789

theorem tailTrace_2492940 : CollatzResearch.WordTrace tailWord_2492940 prefixEnd_2492940 853384308546387729656789 := by
  unfold tailWord_2492940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45462495794255807550302137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60616661059007743400402849 45462495794255807550302137)
  ·
    refine ⟨34096871845691855662726603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45462495794255807550302137 34096871845691855662726603)
    ·
      refine ⟨51145307768537783494089905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34096871845691855662726603 51145307768537783494089905)
      ·
        refine ⟨38358980826403337620567429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51145307768537783494089905 38358980826403337620567429)
        ·
          refine ⟨7192308904950625803856393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38358980826403337620567429 7192308904950625803856393)
          ·
            refine ⟨5394231678712969352892295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7192308904950625803856393 5394231678712969352892295)
            ·
              refine ⟨8091347518069454029338443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394231678712969352892295 8091347518069454029338443)
              ·
                refine ⟨12137021277104181044007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091347518069454029338443 12137021277104181044007665)
                ·
                  refine ⟨9102765957828135783005749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12137021277104181044007665 9102765957828135783005749)
                  ·
                    refine ⟨853384308546387729656789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9102765957828135783005749 853384308546387729656789)
                    ·
                      rfl

theorem cell22_2492940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2492940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492940 prefixEnd_2492940 := by exact prefixLift 2492940
  have htrace : WordTrace (prefixWord ++ tailWord_2492940) baseStart_2492940 baseEnd_2492940 := by
    simpa [prefixWord, tailWord_2492940, baseEnd_2492940] using wordTrace_append hprefix tailTrace_2492940
  have hstable : (prefixWord ++ tailWord_2492940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492940).length < 2 ^ (prefixWord ++ tailWord_2492940).sum := by decide
  have hdescent : baseEnd_2492940 < baseStart_2492940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492953 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 6]
def baseStart_2492953 : Nat := 118140960795 + 2492953 * 2 ^ 59
def prefixEnd_2492953 : Nat := 4983230072969 + 3 ^ 40 * 2492953 * 2
def baseEnd_2492953 : Nat := 284462919570686676360583

theorem tailTrace_2492953 : CollatzResearch.WordTrace tailWord_2492953 prefixEnd_2492953 284462919570686676360583 := by
  unfold tailWord_2492953
  simp only [CollatzResearch.WordTrace]
  refine ⟨90925465737464518320827513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60616977158309678880551675 90925465737464518320827513)
  ·
    refine ⟨68194099303098388740620635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90925465737464518320827513 68194099303098388740620635)
    ·
      refine ⟨102291148954647583110930953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68194099303098388740620635 102291148954647583110930953)
      ·
        refine ⟨76718361715985687333198215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102291148954647583110930953 76718361715985687333198215)
        ·
          refine ⟨115077542573978530999797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76718361715985687333198215 115077542573978530999797323)
          ·
            refine ⟨172616313860967796499695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115077542573978530999797323 172616313860967796499695985)
            ·
              refine ⟨129462235395725847374771989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172616313860967796499695985 129462235395725847374771989)
              ·
                refine ⟨6068542284174649095692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129462235395725847374771989 6068542284174649095692437)
                ·
                  refine ⟨284462919570686676360583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6068542284174649095692437 284462919570686676360583)
                  ·
                    rfl

theorem cell22_2492953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_2492953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2492953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2492953 prefixEnd_2492953 := by exact prefixLift 2492953
  have htrace : WordTrace (prefixWord ++ tailWord_2492953) baseStart_2492953 baseEnd_2492953 := by
    simpa [prefixWord, tailWord_2492953, baseEnd_2492953] using wordTrace_append hprefix tailTrace_2492953
  have hstable : (prefixWord ++ tailWord_2492953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492953).length < 2 ^ (prefixWord ++ tailWord_2492953).sum := by decide
  have hdescent : baseEnd_2492953 < baseStart_2492953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493002 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2493002 : Nat := 118140960795 + 2493002 * 2 ^ 59
def prefixEnd_2493002 : Nat := 4983230072969 + 3 ^ 40 * 2493002 * 2
def baseEnd_2493002 : Nat := 853405532413440234606599

theorem tailTrace_2493002 : CollatzResearch.WordTrace tailWord_2493002 prefixEnd_2493002 853405532413440234606599 := by
  unfold tailWord_2493002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22731813228571749922340315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60618168609524666459574173 22731813228571749922340315)
  ·
    refine ⟨34097719842857624883510473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22731813228571749922340315 34097719842857624883510473)
    ·
      refine ⟨25573289882143218662632855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34097719842857624883510473 25573289882143218662632855)
      ·
        refine ⟨38359934823214827993949283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25573289882143218662632855 38359934823214827993949283)
        ·
          refine ⟨57539902234822241990923925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38359934823214827993949283 57539902234822241990923925)
          ·
            refine ⟨2697182917257292593324559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57539902234822241990923925 2697182917257292593324559)
            ·
              refine ⟨4045774375885938889986839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697182917257292593324559 4045774375885938889986839)
              ·
                refine ⟨6068661563828908334980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045774375885938889986839 6068661563828908334980259)
                ·
                  refine ⟨9102992345743362502470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068661563828908334980259 9102992345743362502470389)
                  ·
                    refine ⟨853405532413440234606599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9102992345743362502470389 853405532413440234606599)
                    ·
                      rfl

theorem cell22_2493002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2493002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493002 prefixEnd_2493002 := by exact prefixLift 2493002
  have htrace : WordTrace (prefixWord ++ tailWord_2493002) baseStart_2493002 baseEnd_2493002 := by
    simpa [prefixWord, tailWord_2493002, baseEnd_2493002] using wordTrace_append hprefix tailTrace_2493002
  have hstable : (prefixWord ++ tailWord_2493002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493002).length < 2 ^ (prefixWord ++ tailWord_2493002).sum := by decide
  have hdescent : baseEnd_2493002 < baseStart_2493002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493032 : List Nat := [2, 1, 4, 3, 2, 2, 8]
def baseStart_2493032 : Nat := 118140960795 + 2493032 * 2 ^ 59
def prefixEnd_2493032 : Nat := 4983230072969 + 3 ^ 40 * 2493032 * 2
def baseEnd_2493032 : Nat := 31607992667649265050241

theorem tailTrace_2493032 : CollatzResearch.WordTrace tailWord_2493032 prefixEnd_2493032 31607992667649265050241 := by
  unfold tailWord_2493032
  simp only [CollatzResearch.WordTrace]
  refine ⟨45464173552089157406476675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60618898069452209875302233 45464173552089157406476675)
  ·
    refine ⟨68196260328133736109715013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45464173552089157406476675 68196260328133736109715013)
    ·
      refine ⟨12786798811525075520571565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68196260328133736109715013 12786798811525075520571565)
      ·
        refine ⟨4795049554321903320214337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12786798811525075520571565 4795049554321903320214337)
        ·
          refine ⟨3596287165741427490160753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795049554321903320214337 3596287165741427490160753)
          ·
            refine ⟨2697215374306070617620565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596287165741427490160753 2697215374306070617620565)
            ·
              refine ⟨31607992667649265050241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2697215374306070617620565 31607992667649265050241)
              ·
                rfl

theorem cell22_2493032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 8].length) (baseStart_2493032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493032 prefixEnd_2493032 := by exact prefixLift 2493032
  have htrace : WordTrace (prefixWord ++ tailWord_2493032) baseStart_2493032 baseEnd_2493032 := by
    simpa [prefixWord, tailWord_2493032, baseEnd_2493032] using wordTrace_append hprefix tailTrace_2493032
  have hstable : (prefixWord ++ tailWord_2493032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493032).length < 2 ^ (prefixWord ++ tailWord_2493032).sum := by decide
  have hdescent : baseEnd_2493032 < baseStart_2493032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493047 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 3, 3]
def baseStart_2493047 : Nat := 118140960795 + 2493047 * 2 ^ 59
def prefixEnd_2493047 : Nat := 4983230072969 + 3 ^ 40 * 2493047 * 2
def baseEnd_2493047 : Nat := 853420936833075117231461

theorem tailTrace_2493047 : CollatzResearch.WordTrace tailWord_2493047 prefixEnd_2493047 853420936833075117231461 := by
  unfold tailWord_2493047
  simp only [CollatzResearch.WordTrace]
  refine ⟨90928894199123972374749395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60619262799415981583166263 90928894199123972374749395)
  ·
    refine ⟨136393341298685958562124093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90928894199123972374749395 136393341298685958562124093)
    ·
      refine ⟨51147502987007234460796535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136393341298685958562124093 51147502987007234460796535)
      ·
        refine ⟨76721254480510851691194803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51147502987007234460796535 76721254480510851691194803)
        ·
          refine ⟨115081881720766277536792205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76721254480510851691194803 115081881720766277536792205)
          ·
            refine ⟨43155705645287354076297077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115081881720766277536792205 43155705645287354076297077)
            ·
              refine ⟨4045847404245689444652851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43155705645287354076297077 4045847404245689444652851)
              ·
                refine ⟨6068771106368534166979277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045847404245689444652851 6068771106368534166979277)
                ·
                  refine ⟨2275789164888200312617229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6068771106368534166979277 2275789164888200312617229)
                  ·
                    refine ⟨853420936833075117231461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275789164888200312617229 853420936833075117231461)
                    ·
                      rfl

theorem cell22_2493047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_2493047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493047 prefixEnd_2493047 := by exact prefixLift 2493047
  have htrace : WordTrace (prefixWord ++ tailWord_2493047) baseStart_2493047 baseEnd_2493047 := by
    simpa [prefixWord, tailWord_2493047, baseEnd_2493047] using wordTrace_append hprefix tailTrace_2493047
  have hstable : (prefixWord ++ tailWord_2493047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493047).length < 2 ^ (prefixWord ++ tailWord_2493047).sum := by decide
  have hdescent : baseEnd_2493047 < baseStart_2493047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493053 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_2493053 : Nat := 118140960795 + 2493053 * 2 ^ 59
def prefixEnd_2493053 : Nat := 4983230072969 + 3 ^ 40 * 2493053 * 2
def baseEnd_2493053 : Nat := 853422990755693101581443

theorem tailTrace_2493053 : CollatzResearch.WordTrace tailWord_2493053 prefixEnd_2493053 853422990755693101581443 := by
  unfold tailWord_2493053
  simp only [CollatzResearch.WordTrace]
  refine ⟨90929113037102235399467813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60619408691401490266311875 90929113037102235399467813)
  ·
    refine ⟨17049208694456669137400215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90929113037102235399467813 17049208694456669137400215)
    ·
      refine ⟨25573813041685003706100323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17049208694456669137400215 25573813041685003706100323)
      ·
        refine ⟨38360719562527505559150485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25573813041685003706100323 38360719562527505559150485)
        ·
          refine ⟨1798158729493476823085179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38360719562527505559150485 1798158729493476823085179)
          ·
            refine ⟨2697238094240215234627769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798158729493476823085179 2697238094240215234627769)
            ·
              refine ⟨2022928570680161425970827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697238094240215234627769 2022928570680161425970827)
              ·
                refine ⟨3034392856020242138956241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022928570680161425970827 3034392856020242138956241)
                ·
                  refine ⟨2275794642015181604217181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034392856020242138956241 2275794642015181604217181)
                  ·
                    refine ⟨853422990755693101581443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275794642015181604217181 853422990755693101581443)
                    ·
                      rfl

theorem cell22_2493053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_2493053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493053 prefixEnd_2493053 := by exact prefixLift 2493053
  have htrace : WordTrace (prefixWord ++ tailWord_2493053) baseStart_2493053 baseEnd_2493053 := by
    simpa [prefixWord, tailWord_2493053, baseEnd_2493053] using wordTrace_append hprefix tailTrace_2493053
  have hstable : (prefixWord ++ tailWord_2493053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493053).length < 2 ^ (prefixWord ++ tailWord_2493053).sum := by decide
  have hdescent : baseEnd_2493053 < baseStart_2493053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493137 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_2493137 : Nat := 118140960795 + 2493137 * 2 ^ 59
def prefixEnd_2493137 : Nat := 4983230072969 + 3 ^ 40 * 2493137 * 2
def baseEnd_2493137 : Nat := 853451745672344882481185

theorem tailTrace_2493137 : CollatzResearch.WordTrace tailWord_2493137 prefixEnd_2493137 853451745672344882481185 := by
  unfold tailWord_2493137
  simp only [CollatzResearch.WordTrace]
  refine ⟨90932176768797917745525665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60621451179198611830350443 90932176768797917745525665)
  ·
    refine ⟨68199132576598438309144249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90932176768797917745525665 68199132576598438309144249)
    ·
      refine ⟨51149349432448828731858187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68199132576598438309144249 51149349432448828731858187)
      ·
        refine ⟨76724024148673243097787281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51149349432448828731858187 76724024148673243097787281)
        ·
          refine ⟨57543018111504932323340461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76724024148673243097787281 57543018111504932323340461)
          ·
            refine ⟨21578631791814349621252673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57543018111504932323340461 21578631791814349621252673)
            ·
              refine ⟨16183973843860762215939505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21578631791814349621252673 16183973843860762215939505)
              ·
                refine ⟨12137980382895571661954629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16183973843860762215939505 12137980382895571661954629)
                ·
                  refine ⟨2275871321792919686616493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12137980382895571661954629 2275871321792919686616493)
                  ·
                    refine ⟨853451745672344882481185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275871321792919686616493 853451745672344882481185)
                    ·
                      rfl

theorem cell22_2493137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_2493137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493137 prefixEnd_2493137 := by exact prefixLift 2493137
  have htrace : WordTrace (prefixWord ++ tailWord_2493137) baseStart_2493137 baseEnd_2493137 := by
    simpa [prefixWord, tailWord_2493137, baseEnd_2493137] using wordTrace_append hprefix tailTrace_2493137
  have hstable : (prefixWord ++ tailWord_2493137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493137).length < 2 ^ (prefixWord ++ tailWord_2493137).sum := by decide
  have hdescent : baseEnd_2493137 < baseStart_2493137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493141 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2493141 : Nat := 118140960795 + 2493141 * 2 ^ 59
def prefixEnd_2493141 : Nat := 4983230072969 + 3 ^ 40 * 2493141 * 2
def baseEnd_2493141 : Nat := 853453114954090205381173

theorem tailTrace_2493141 : CollatzResearch.WordTrace tailWord_2493141 prefixEnd_2493141 853453114954090205381173 := by
  unfold tailWord_2493141
  simp only [CollatzResearch.WordTrace]
  refine ⟨90932322660783426428671277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60621548440522284285780851 90932322660783426428671277)
  ·
    refine ⟨34099620997793784910751729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90932322660783426428671277 34099620997793784910751729)
    ·
      refine ⟨25574715748345338683063797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34099620997793784910751729 25574715748345338683063797)
      ·
        refine ⟨2397629601407375501537231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25574715748345338683063797 2397629601407375501537231)
        ·
          refine ⟨3596444402111063252305847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397629601407375501537231 3596444402111063252305847)
          ·
            refine ⟨5394666603166594878458771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596444402111063252305847 5394666603166594878458771)
            ·
              refine ⟨8091999904749892317688157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394666603166594878458771 8091999904749892317688157)
              ·
                refine ⟨3034499964281209619133059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8091999904749892317688157 3034499964281209619133059)
                ·
                  refine ⟨4551749946421814428699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034499964281209619133059 4551749946421814428699589)
                  ·
                    refine ⟨853453114954090205381173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4551749946421814428699589 853453114954090205381173)
                    ·
                      rfl

theorem cell22_2493141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2493141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493141 prefixEnd_2493141 := by exact prefixLift 2493141
  have htrace : WordTrace (prefixWord ++ tailWord_2493141) baseStart_2493141 baseEnd_2493141 := by
    simpa [prefixWord, tailWord_2493141, baseEnd_2493141] using wordTrace_append hprefix tailTrace_2493141
  have hstable : (prefixWord ++ tailWord_2493141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493141).length < 2 ^ (prefixWord ++ tailWord_2493141).sum := by decide
  have hdescent : baseEnd_2493141 < baseStart_2493141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493212 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_2493212 : Nat := 118140960795 + 2493212 * 2 ^ 59
def prefixEnd_2493212 : Nat := 4983230072969 + 3 ^ 40 * 2493212 * 2
def baseEnd_2493212 : Nat := 284492473235023228951985

theorem tailTrace_2493212 : CollatzResearch.WordTrace tailWord_2493212 prefixEnd_2493212 284492473235023228951985 := by
  unfold tailWord_2493212
  simp only [CollatzResearch.WordTrace]
  refine ⟨45467456121763102777252945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60623274829017470369670593 45467456121763102777252945)
  ·
    refine ⟨34100592091322327082939709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45467456121763102777252945 34100592091322327082939709)
    ·
      refine ⟨12787722034245872656102391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34100592091322327082939709 12787722034245872656102391)
      ·
        refine ⟨19181583051368808984153587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12787722034245872656102391 19181583051368808984153587)
        ·
          refine ⟨28772374577053213476230381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19181583051368808984153587 28772374577053213476230381)
          ·
            refine ⟨10789640466394955053586393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28772374577053213476230381 10789640466394955053586393)
            ·
              refine ⟨8092230349796216290189795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10789640466394955053586393 8092230349796216290189795)
              ·
                refine ⟨12138345524694324435284693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8092230349796216290189795 12138345524694324435284693)
                ·
                  refine ⟨284492473235023228951985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12138345524694324435284693 284492473235023228951985)
                  ·
                    rfl

theorem cell22_2493212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_2493212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493212 prefixEnd_2493212 := by exact prefixLift 2493212
  have htrace : WordTrace (prefixWord ++ tailWord_2493212) baseStart_2493212 baseEnd_2493212 := by
    simpa [prefixWord, tailWord_2493212, baseEnd_2493212] using wordTrace_append hprefix tailTrace_2493212
  have hstable : (prefixWord ++ tailWord_2493212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493212).length < 2 ^ (prefixWord ++ tailWord_2493212).sum := by decide
  have hdescent : baseEnd_2493212 < baseStart_2493212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493216 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_2493216 : Nat := 118140960795 + 2493216 * 2 ^ 59
def prefixEnd_2493216 : Nat := 4983230072969 + 3 ^ 40 * 2493216 * 2
def baseEnd_2493216 : Nat := 853478788986815009755943

theorem tailTrace_2493216 : CollatzResearch.WordTrace tailWord_2493216 prefixEnd_2493216 853478788986815009755943 := by
  unfold tailWord_2493216
  simp only [CollatzResearch.WordTrace]
  refine ⟨45467529067755857118825751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60623372090341142825101001 45467529067755857118825751)
  ·
    refine ⟨68201293601633785678238627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45467529067755857118825751 68201293601633785678238627)
    ·
      refine ⟨102301940402450678517357941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68201293601633785678238627 102301940402450678517357941)
      ·
        refine ⟨9590806912729751111002307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102301940402450678517357941 9590806912729751111002307)
        ·
          refine ⟨14386210369094626666503461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590806912729751111002307 14386210369094626666503461)
          ·
            refine ⟨2697414444205242499969399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14386210369094626666503461 2697414444205242499969399)
            ·
              refine ⟨4046121666307863749954099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697414444205242499969399 4046121666307863749954099)
              ·
                refine ⟨6069182499461795624931149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046121666307863749954099 6069182499461795624931149)
                ·
                  refine ⟨2275943437298173359349181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6069182499461795624931149 2275943437298173359349181)
                  ·
                    refine ⟨853478788986815009755943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275943437298173359349181 853478788986815009755943)
                    ·
                      rfl

theorem cell22_2493216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_2493216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493216 prefixEnd_2493216 := by exact prefixLift 2493216
  have htrace : WordTrace (prefixWord ++ tailWord_2493216) baseStart_2493216 baseEnd_2493216 := by
    simpa [prefixWord, tailWord_2493216, baseEnd_2493216] using wordTrace_append hprefix tailTrace_2493216
  have hstable : (prefixWord ++ tailWord_2493216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493216).length < 2 ^ (prefixWord ++ tailWord_2493216).sum := by decide
  have hdescent : baseEnd_2493216 < baseStart_2493216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493340 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2493340 : Nat := 118140960795 + 2493340 * 2 ^ 59
def prefixEnd_2493340 : Nat := 4983230072969 + 3 ^ 40 * 2493340 * 2
def baseEnd_2493340 : Nat := 853521236720920019655563

theorem tailTrace_2493340 : CollatzResearch.WordTrace tailWord_2493340 prefixEnd_2493340 853521236720920019655563 := by
  unfold tailWord_2493340
  simp only [CollatzResearch.WordTrace]
  refine ⟨45469790393531241707582737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60626387191374988943443649 45469790393531241707582737)
  ·
    refine ⟨34102342795148431280687053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45469790393531241707582737 34102342795148431280687053)
    ·
      refine ⟨12788378548180661730257645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34102342795148431280687053 12788378548180661730257645)
      ·
        refine ⟨4795641955567748148846617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12788378548180661730257645 4795641955567748148846617)
        ·
          refine ⟨3596731466675811111634963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795641955567748148846617 3596731466675811111634963)
          ·
            refine ⟨5395097200013716667452445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596731466675811111634963 5395097200013716667452445)
            ·
              refine ⟨2023161450005143750294667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5395097200013716667452445 2023161450005143750294667)
              ·
                refine ⟨3034742175007715625442001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023161450005143750294667 3034742175007715625442001)
                ·
                  refine ⟨2276056631255786719081501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034742175007715625442001 2276056631255786719081501)
                  ·
                    refine ⟨853521236720920019655563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276056631255786719081501 853521236720920019655563)
                    ·
                      rfl

theorem cell22_2493340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2493340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493340 prefixEnd_2493340 := by exact prefixLift 2493340
  have htrace : WordTrace (prefixWord ++ tailWord_2493340) baseStart_2493340 baseEnd_2493340 := by
    simpa [prefixWord, tailWord_2493340, baseEnd_2493340] using wordTrace_append hprefix tailTrace_2493340
  have hstable : (prefixWord ++ tailWord_2493340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493340).length < 2 ^ (prefixWord ++ tailWord_2493340).sum := by decide
  have hdescent : baseEnd_2493340 < baseStart_2493340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493368 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_2493368 : Nat := 118140960795 + 2493368 * 2 ^ 59
def prefixEnd_2493368 : Nat := 4983230072969 + 3 ^ 40 * 2493368 * 2
def baseEnd_2493368 : Nat := 853530821693137279955477

theorem tailTrace_2493368 : CollatzResearch.WordTrace tailWord_2493368 prefixEnd_2493368 853530821693137279955477 := by
  unfold tailWord_2493368
  simp only [CollatzResearch.WordTrace]
  refine ⟨45470301015480522098592379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60627068020640696131456505 45470301015480522098592379)
  ·
    refine ⟨68205451523220783147888569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45470301015480522098592379 68205451523220783147888569)
    ·
      refine ⟨51154088642415587360916427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68205451523220783147888569 51154088642415587360916427)
      ·
        refine ⟨76731132963623381041374641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51154088642415587360916427 76731132963623381041374641)
        ·
          refine ⟨57548349722717535781030981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76731132963623381041374641 57548349722717535781030981)
          ·
            refine ⟨10790315573009537958943309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57548349722717535781030981 10790315573009537958943309)
            ·
              refine ⟨4046368339878576734603741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10790315573009537958943309 4046368339878576734603741)
              ·
                refine ⟨1517388127454466275476403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4046368339878576734603741 1517388127454466275476403)
                ·
                  refine ⟨2276082191181699413214605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517388127454466275476403 2276082191181699413214605)
                  ·
                    refine ⟨853530821693137279955477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276082191181699413214605 853530821693137279955477)
                    ·
                      rfl

theorem cell22_2493368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_2493368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493368 prefixEnd_2493368 := by exact prefixLift 2493368
  have htrace : WordTrace (prefixWord ++ tailWord_2493368) baseStart_2493368 baseEnd_2493368 := by
    simpa [prefixWord, tailWord_2493368, baseEnd_2493368] using wordTrace_append hprefix tailTrace_2493368
  have hstable : (prefixWord ++ tailWord_2493368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493368).length < 2 ^ (prefixWord ++ tailWord_2493368).sum := by decide
  have hdescent : baseEnd_2493368 < baseStart_2493368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493398 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2493398 : Nat := 118140960795 + 2493398 * 2 ^ 59
def prefixEnd_2493398 : Nat := 4983230072969 + 3 ^ 40 * 2493398 * 2
def baseEnd_2493398 : Nat := 284513697102075733901795

theorem tailTrace_2493398 : CollatzResearch.WordTrace tailWord_2493398 prefixEnd_2493398 284513697102075733901795 := by
  unfold tailWord_2493398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683856013803272457548553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60627797480568239547184565 5683856013803272457548553)
  ·
    refine ⟨4262892010352454343161415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5683856013803272457548553 4262892010352454343161415)
    ·
      refine ⟨6394338015528681514742123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262892010352454343161415 6394338015528681514742123)
      ·
        refine ⟨9591507023293022272113185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394338015528681514742123 9591507023293022272113185)
        ·
          refine ⟨7193630267469766704084889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9591507023293022272113185 7193630267469766704084889)
          ·
            refine ⟨5395222700602325028063667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7193630267469766704084889 5395222700602325028063667)
            ·
              refine ⟨8092834050903487542095501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395222700602325028063667 8092834050903487542095501)
              ·
                refine ⟨3034812769088807828285813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8092834050903487542095501 3034812769088807828285813)
                ·
                  refine ⟨284513697102075733901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3034812769088807828285813 284513697102075733901795)
                  ·
                    rfl

theorem cell22_2493398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2493398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493398 prefixEnd_2493398 := by exact prefixLift 2493398
  have htrace : WordTrace (prefixWord ++ tailWord_2493398) baseStart_2493398 baseEnd_2493398 := by
    simpa [prefixWord, tailWord_2493398, baseEnd_2493398] using wordTrace_append hprefix tailTrace_2493398
  have hstable : (prefixWord ++ tailWord_2493398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493398).length < 2 ^ (prefixWord ++ tailWord_2493398).sum := by decide
  have hdescent : baseEnd_2493398 < baseStart_2493398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493471 : List Nat := [1, 1, 2, 4, 1, 4, 3, 6]
def baseStart_2493471 : Nat := 118140960795 + 2493471 * 2 ^ 59
def prefixEnd_2493471 : Nat := 4983230072969 + 3 ^ 40 * 2493471 * 2
def baseEnd_2493471 : Nat := 94840675633119927181129

theorem tailTrace_2493471 : CollatzResearch.WordTrace tailWord_2493471 prefixEnd_2493471 94840675633119927181129 := by
  unfold tailWord_2493471
  simp only [CollatzResearch.WordTrace]
  refine ⟨90944358749587892788184267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60629572499725261858789511 90944358749587892788184267)
  ·
    refine ⟨136416538124381839182276401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90944358749587892788184267 136416538124381839182276401)
    ·
      refine ⟨102312403593286379386707301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136416538124381839182276401 102312403593286379386707301)
      ·
        refine ⟨19183575673741196135007619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102312403593286379386707301 19183575673741196135007619)
        ·
          refine ⟨28775363510611794202511429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19183575673741196135007619 28775363510611794202511429)
          ·
            refine ⟨5395380658239711412970893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28775363510611794202511429 5395380658239711412970893)
            ·
              refine ⟨2023267746839891779864085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5395380658239711412970893 2023267746839891779864085)
              ·
                refine ⟨94840675633119927181129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2023267746839891779864085 94840675633119927181129)
                ·
                  rfl

theorem cell22_2493471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 6].length) (baseStart_2493471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493471 prefixEnd_2493471 := by exact prefixLift 2493471
  have htrace : WordTrace (prefixWord ++ tailWord_2493471) baseStart_2493471 baseEnd_2493471 := by
    simpa [prefixWord, tailWord_2493471, baseEnd_2493471] using wordTrace_append hprefix tailTrace_2493471
  have hstable : (prefixWord ++ tailWord_2493471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493471).length < 2 ^ (prefixWord ++ tailWord_2493471).sum := by decide
  have hdescent : baseEnd_2493471 < baseStart_2493471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493473 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2493473 : Nat := 118140960795 + 2493473 * 2 ^ 59
def prefixEnd_2493473 : Nat := 4983230072969 + 3 ^ 40 * 2493473 * 2
def baseEnd_2493473 : Nat := 853566765338952006080155

theorem tailTrace_2493473 : CollatzResearch.WordTrace tailWord_2493473 prefixEnd_2493473 853566765338952006080155 := by
  unfold tailWord_2493473
  simp only [CollatzResearch.WordTrace]
  refine ⟨90944431695580647129757073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60629621130387098086504715 90944431695580647129757073)
  ·
    refine ⟨68208323771685485347317805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90944431695580647129757073 68208323771685485347317805)
    ·
      refine ⟨25578121414382057005244177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68208323771685485347317805 25578121414382057005244177)
      ·
        refine ⟨19183591060786542753933133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25578121414382057005244177 19183591060786542753933133)
        ·
          refine ⟨7193846647794953532724925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19183591060786542753933133 7193846647794953532724925)
          ·
            refine ⟨2697692492923107574771847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7193846647794953532724925 2697692492923107574771847)
            ·
              refine ⟨4046538739384661362157771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697692492923107574771847 4046538739384661362157771)
              ·
                refine ⟨6069808109076992043236657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046538739384661362157771 6069808109076992043236657)
                ·
                  refine ⟨4552356081807744032427493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6069808109076992043236657 4552356081807744032427493)
                  ·
                    refine ⟨853566765338952006080155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552356081807744032427493 853566765338952006080155)
                    ·
                      rfl

theorem cell22_2493473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2493473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493473 prefixEnd_2493473 := by exact prefixLift 2493473
  have htrace : WordTrace (prefixWord ++ tailWord_2493473) baseStart_2493473 baseEnd_2493473 := by
    simpa [prefixWord, tailWord_2493473, baseEnd_2493473] using wordTrace_append hprefix tailTrace_2493473
  have hstable : (prefixWord ++ tailWord_2493473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493473).length < 2 ^ (prefixWord ++ tailWord_2493473).sum := by decide
  have hdescent : baseEnd_2493473 < baseStart_2493473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493492 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2493492 : Nat := 118140960795 + 2493492 * 2 ^ 59
def prefixEnd_2493492 : Nat := 4983230072969 + 3 ^ 40 * 2493492 * 2
def baseEnd_2493492 : Nat := 853573269427242289855097

theorem tailTrace_2493492 : CollatzResearch.WordTrace tailWord_2493492 prefixEnd_2493492 853573269427242289855097 := by
  unfold tailWord_2493492
  simp only [CollatzResearch.WordTrace]
  refine ⟨45472562341255906687349365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60630083121674542249799153 45472562341255906687349365)
  ·
    refine ⟨4263052719492741251939003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45472562341255906687349365 4263052719492741251939003)
    ·
      refine ⟨6394579079239111877908505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263052719492741251939003 6394579079239111877908505)
      ·
        refine ⟨4795934309429333908431379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6394579079239111877908505 4795934309429333908431379)
        ·
          refine ⟨7193901464144000862647069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795934309429333908431379 7193901464144000862647069)
          ·
            refine ⟨2697713049054000323492651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7193901464144000862647069 2697713049054000323492651)
            ·
              refine ⟨4046569573581000485238977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697713049054000323492651 4046569573581000485238977)
              ·
                refine ⟨3034927180185750363929233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046569573581000485238977 3034927180185750363929233)
                ·
                  refine ⟨2276195385139312772946925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034927180185750363929233 2276195385139312772946925)
                  ·
                    refine ⟨853573269427242289855097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276195385139312772946925 853573269427242289855097)
                    ·
                      rfl

theorem cell22_2493492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2493492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493492 prefixEnd_2493492 := by exact prefixLift 2493492
  have htrace : WordTrace (prefixWord ++ tailWord_2493492) baseStart_2493492 baseEnd_2493492 := by
    simpa [prefixWord, tailWord_2493492, baseEnd_2493492] using wordTrace_append hprefix tailTrace_2493492
  have hstable : (prefixWord ++ tailWord_2493492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493492).length < 2 ^ (prefixWord ++ tailWord_2493492).sum := by decide
  have hdescent : baseEnd_2493492 < baseStart_2493492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493655 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2493655 : Nat := 118140960795 + 2493655 * 2 ^ 59
def prefixEnd_2493655 : Nat := 4983230072969 + 3 ^ 40 * 2493655 * 2
def baseEnd_2493655 : Nat := 853629067658364198029597

theorem tailTrace_2493655 : CollatzResearch.WordTrace tailWord_2493655 prefixEnd_2493655 853629067658364198029597 := by
  unfold tailWord_2493655
  simp only [CollatzResearch.WordTrace]
  refine ⟨90951069780921292212882419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60634046520614194808588279 90951069780921292212882419)
  ·
    refine ⟨136426604671381938319323629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90951069780921292212882419 136426604671381938319323629)
    ·
      refine ⟨51159976751768226869746361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136426604671381938319323629 51159976751768226869746361)
      ·
        refine ⟨38369982563826170152309771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51159976751768226869746361 38369982563826170152309771)
        ·
          refine ⟨57554973845739255228464657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38369982563826170152309771 57554973845739255228464657)
          ·
            refine ⟨43166230384304441421348493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57554973845739255228464657 43166230384304441421348493)
            ·
              refine ⟨16187336394114165533005685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43166230384304441421348493 16187336394114165533005685)
              ·
                refine ⟨1517562786948203018719283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16187336394114165533005685 1517562786948203018719283)
                ·
                  refine ⟨2276344180422304528078925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517562786948203018719283 2276344180422304528078925)
                  ·
                    refine ⟨853629067658364198029597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276344180422304528078925 853629067658364198029597)
                    ·
                      rfl

theorem cell22_2493655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2493655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493655 prefixEnd_2493655 := by exact prefixLift 2493655
  have htrace : WordTrace (prefixWord ++ tailWord_2493655) baseStart_2493655 baseEnd_2493655 := by
    simpa [prefixWord, tailWord_2493655, baseEnd_2493655] using wordTrace_append hprefix tailTrace_2493655
  have hstable : (prefixWord ++ tailWord_2493655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493655).length < 2 ^ (prefixWord ++ tailWord_2493655).sum := by decide
  have hdescent : baseEnd_2493655 < baseStart_2493655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493668 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2493668 : Nat := 118140960795 + 2493668 * 2 ^ 59
def prefixEnd_2493668 : Nat := 4983230072969 + 3 ^ 40 * 2493668 * 2
def baseEnd_2493668 : Nat := 284544505941345499151519

theorem tailTrace_2493668 : CollatzResearch.WordTrace tailWord_2493668 prefixEnd_2493668 284544505941345499151519 := by
  unfold tailWord_2493668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45475771964937097716552829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60634362619916130288737105 45475771964937097716552829)
  ·
    refine ⟨17053414486851411643707311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45475771964937097716552829 17053414486851411643707311)
    ·
      refine ⟨25580121730277117465560967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053414486851411643707311 25580121730277117465560967)
      ·
        refine ⟨38370182595415676198341451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25580121730277117465560967 38370182595415676198341451)
        ·
          refine ⟨57555273893123514297512177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38370182595415676198341451 57555273893123514297512177)
          ·
            refine ⟨43166455419842635723134133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57555273893123514297512177 43166455419842635723134133)
            ·
              refine ⟨4046855195610247099043825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43166455419842635723134133 4046855195610247099043825)
              ·
                refine ⟨3035141396707685324282869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046855195610247099043825 3035141396707685324282869)
                ·
                  refine ⟨284544505941345499151519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3035141396707685324282869 284544505941345499151519)
                  ·
                    rfl

theorem cell22_2493668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2493668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493668 prefixEnd_2493668 := by exact prefixLift 2493668
  have htrace : WordTrace (prefixWord ++ tailWord_2493668) baseStart_2493668 baseEnd_2493668 := by
    simpa [prefixWord, tailWord_2493668, baseEnd_2493668] using wordTrace_append hprefix tailTrace_2493668
  have hstable : (prefixWord ++ tailWord_2493668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493668).length < 2 ^ (prefixWord ++ tailWord_2493668).sum := by decide
  have hdescent : baseEnd_2493668 < baseStart_2493668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493758 : List Nat := [4, 2, 1, 2, 1, 1, 1, 10]
def baseStart_2493758 : Nat := 118140960795 + 2493758 * 2 ^ 59
def prefixEnd_2493758 : Nat := 4983230072969 + 3 ^ 40 * 2493758 * 2
def baseEnd_2493758 : Nat := 94851591851478473633809

theorem tailTrace_2493758 : CollatzResearch.WordTrace tailWord_2493758 prefixEnd_2493758 94851591851478473633809 := by
  unfold tailWord_2493758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369353312443517600485241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60636550999698760535921285 11369353312443517600485241)
  ·
    refine ⟨8527014984332638200363931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11369353312443517600485241 8527014984332638200363931)
    ·
      refine ⟨12790522476498957300545897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8527014984332638200363931 12790522476498957300545897)
      ·
        refine ⟨9592891857374217975409423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12790522476498957300545897 9592891857374217975409423)
        ·
          refine ⟨14389337786061326963114135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9592891857374217975409423 14389337786061326963114135)
          ·
            refine ⟨21584006679091990444671203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14389337786061326963114135 21584006679091990444671203)
            ·
              refine ⟨32376010018637985667006805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21584006679091990444671203 32376010018637985667006805)
              ·
                refine ⟨94851591851478473633809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32376010018637985667006805 94851591851478473633809)
                ·
                  rfl

theorem cell22_2493758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_2493758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493758 prefixEnd_2493758 := by exact prefixLift 2493758
  have htrace : WordTrace (prefixWord ++ tailWord_2493758) baseStart_2493758 baseEnd_2493758 := by
    simpa [prefixWord, tailWord_2493758, baseEnd_2493758] using wordTrace_append hprefix tailTrace_2493758
  have hstable : (prefixWord ++ tailWord_2493758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493758).length < 2 ^ (prefixWord ++ tailWord_2493758).sum := by decide
  have hdescent : baseEnd_2493758 < baseStart_2493758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493880 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_2493880 : Nat := 118140960795 + 2493880 * 2 ^ 59
def prefixEnd_2493880 : Nat := 4983230072969 + 3 ^ 40 * 2493880 * 2
def baseEnd_2493880 : Nat := 853706089756538611153907

theorem tailTrace_2493880 : CollatzResearch.WordTrace tailWord_2493880 prefixEnd_2493880 853706089756538611153907 := by
  unfold tailWord_2493880
  simp only [CollatzResearch.WordTrace]
  refine ⟨45479638102553077819911547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60639517470070770426548729 45479638102553077819911547)
  ·
    refine ⟨68219457153829616729867321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45479638102553077819911547 68219457153829616729867321)
    ·
      refine ⟨51164592865372212547400491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68219457153829616729867321 51164592865372212547400491)
      ·
        refine ⟨76746889298058318821100737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51164592865372212547400491 76746889298058318821100737)
        ·
          refine ⟨57560166973543739115825553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76746889298058318821100737 57560166973543739115825553)
          ·
            refine ⟨43170125230157804336869165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57560166973543739115825553 43170125230157804336869165)
            ·
              refine ⟨16188796961309176626325937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43170125230157804336869165 16188796961309176626325937)
              ·
                refine ⟨12141597720981882469744453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16188796961309176626325937 12141597720981882469744453)
                ·
                  refine ⟨2276549572684102963077085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12141597720981882469744453 2276549572684102963077085)
                  ·
                    refine ⟨853706089756538611153907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276549572684102963077085 853706089756538611153907)
                    ·
                      rfl

theorem cell22_2493880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_2493880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493880 prefixEnd_2493880 := by exact prefixLift 2493880
  have htrace : WordTrace (prefixWord ++ tailWord_2493880) baseStart_2493880 baseEnd_2493880 := by
    simpa [prefixWord, tailWord_2493880, baseEnd_2493880] using wordTrace_append hprefix tailTrace_2493880
  have hstable : (prefixWord ++ tailWord_2493880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493880).length < 2 ^ (prefixWord ++ tailWord_2493880).sum := by decide
  have hdescent : baseEnd_2493880 < baseStart_2493880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493895 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2493895 : Nat := 118140960795 + 2493895 * 2 ^ 59
def prefixEnd_2493895 : Nat := 4983230072969 + 3 ^ 40 * 2493895 * 2
def baseEnd_2493895 : Nat := 853711224563083572028861

theorem tailTrace_2493895 : CollatzResearch.WordTrace tailWord_2493895 prefixEnd_2493895 853711224563083572028861 := by
  unfold tailWord_2493895
  simp only [CollatzResearch.WordTrace]
  refine ⟨90959823300051813201619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60639882200034542134412759 90959823300051813201619139)
  ·
    refine ⟨136439734950077719802428709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90959823300051813201619139 136439734950077719802428709)
    ·
      refine ⟨25582450303139572462955383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136439734950077719802428709 25582450303139572462955383)
      ·
        refine ⟨38373675454709358694433075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25582450303139572462955383 38373675454709358694433075)
        ·
          refine ⟨57560513182064038041649613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38373675454709358694433075 57560513182064038041649613)
          ·
            refine ⟨21585192443274014265618605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57560513182064038041649613 21585192443274014265618605)
            ·
              refine ⟨8094447166227755349606977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21585192443274014265618605 8094447166227755349606977)
              ·
                refine ⟨6070835374670816512205233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8094447166227755349606977 6070835374670816512205233)
                ·
                  refine ⟨4553126531003112384153925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6070835374670816512205233 4553126531003112384153925)
                  ·
                    refine ⟨853711224563083572028861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553126531003112384153925 853711224563083572028861)
                    ·
                      rfl

theorem cell22_2493895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2493895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493895 prefixEnd_2493895 := by exact prefixLift 2493895
  have htrace : WordTrace (prefixWord ++ tailWord_2493895) baseStart_2493895 baseEnd_2493895 := by
    simpa [prefixWord, tailWord_2493895, baseEnd_2493895] using wordTrace_append hprefix tailTrace_2493895
  have hstable : (prefixWord ++ tailWord_2493895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493895).length < 2 ^ (prefixWord ++ tailWord_2493895).sum := by decide
  have hdescent : baseEnd_2493895 < baseStart_2493895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493914 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_2493914 : Nat := 118140960795 + 2493914 * 2 ^ 59
def prefixEnd_2493914 : Nat := 4983230072969 + 3 ^ 40 * 2493914 * 2
def baseEnd_2493914 : Nat := 853717728651373855803803

theorem tailTrace_2493914 : CollatzResearch.WordTrace tailWord_2493914 prefixEnd_2493914 853717728651373855803803 := by
  unfold tailWord_2493914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22740129071745744861640199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60640344191321986297707197 22740129071745744861640199)
  ·
    refine ⟨34110193607618617292460299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22740129071745744861640199 34110193607618617292460299)
    ·
      refine ⟨51165290411427925938690449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34110193607618617292460299 51165290411427925938690449)
      ·
        refine ⟨38373967808570944454017837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51165290411427925938690449 38373967808570944454017837)
        ·
          refine ⟨14390237928214104170256689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38373967808570944454017837 14390237928214104170256689)
          ·
            refine ⟨10792678446160578127692517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14390237928214104170256689 10792678446160578127692517)
            ·
              refine ⟨2023627208655108398942347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10792678446160578127692517 2023627208655108398942347)
              ·
                refine ⟨3035440812982662598413521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023627208655108398942347 3035440812982662598413521)
                ·
                  refine ⟨2276580609736996948810141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3035440812982662598413521 2276580609736996948810141)
                  ·
                    refine ⟨853717728651373855803803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276580609736996948810141 853717728651373855803803)
                    ·
                      rfl

theorem cell22_2493914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_2493914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493914 prefixEnd_2493914 := by exact prefixLift 2493914
  have htrace : WordTrace (prefixWord ++ tailWord_2493914) baseStart_2493914 baseEnd_2493914 := by
    simpa [prefixWord, tailWord_2493914, baseEnd_2493914] using wordTrace_append hprefix tailTrace_2493914
  have hstable : (prefixWord ++ tailWord_2493914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493914).length < 2 ^ (prefixWord ++ tailWord_2493914).sum := by decide
  have hdescent : baseEnd_2493914 < baseStart_2493914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493950 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2493950 : Nat := 118140960795 + 2493950 * 2 ^ 59
def prefixEnd_2493950 : Nat := 4983230072969 + 3 ^ 40 * 2493950 * 2
def baseEnd_2493950 : Nat := 284576684062360587301231

theorem tailTrace_2493950 : CollatzResearch.WordTrace tailWord_2493950 prefixEnd_2493950 284576684062360587301231 := by
  unfold tailWord_2493950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11370228664356569699358913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60641219543235038396580869 11370228664356569699358913)
  ·
    refine ⟨8527671498267427274519185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11370228664356569699358913 8527671498267427274519185)
    ·
      refine ⟨6395753623700570455889389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527671498267427274519185 6395753623700570455889389)
      ·
        refine ⟨2398407608887713920958521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6395753623700570455889389 2398407608887713920958521)
        ·
          refine ⟨1798805706665785440718891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398407608887713920958521 1798805706665785440718891)
          ·
            refine ⟨2698208559998678161078337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798805706665785440718891 2698208559998678161078337)
            ·
              refine ⟨2023656419999008620808753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698208559998678161078337 2023656419999008620808753)
              ·
                refine ⟨1517742314999256465606565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023656419999008620808753 1517742314999256465606565)
                ·
                  refine ⟨284576684062360587301231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517742314999256465606565 284576684062360587301231)
                  ·
                    rfl

theorem cell22_2493950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2493950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2493950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2493950 prefixEnd_2493950 := by exact prefixLift 2493950
  have htrace : WordTrace (prefixWord ++ tailWord_2493950) baseStart_2493950 baseEnd_2493950 := by
    simpa [prefixWord, tailWord_2493950, baseEnd_2493950] using wordTrace_append hprefix tailTrace_2493950
  have hstable : (prefixWord ++ tailWord_2493950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493950).length < 2 ^ (prefixWord ++ tailWord_2493950).sum := by decide
  have hdescent : baseEnd_2493950 < baseStart_2493950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494006 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2494006 : Nat := 118140960795 + 2494006 * 2 ^ 59
def prefixEnd_2494006 : Nat := 4983230072969 + 3 ^ 40 * 2494006 * 2
def baseEnd_2494006 : Nat := 284583074043838760834507

theorem tailTrace_2494006 : CollatzResearch.WordTrace tailWord_2494006 prefixEnd_2494006 284583074043838760834507 := by
  unfold tailWord_2494006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685241987665604947431867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60642581201766452772606581 5685241987665604947431867)
  ·
    refine ⟨8527862981498407421147801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685241987665604947431867 8527862981498407421147801)
    ·
      refine ⟨6395897236123805565860851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527862981498407421147801 6395897236123805565860851)
      ·
        refine ⟨9593845854185708348791277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395897236123805565860851 9593845854185708348791277)
        ·
          refine ⟨3597692195319640630796729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9593845854185708348791277 3597692195319640630796729)
          ·
            refine ⟨2698269146489730473097547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597692195319640630796729 2698269146489730473097547)
            ·
              refine ⟨4047403719734595709646321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698269146489730473097547 4047403719734595709646321)
              ·
                refine ⟨3035552789800946782234741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4047403719734595709646321 3035552789800946782234741)
                ·
                  refine ⟨284583074043838760834507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3035552789800946782234741 284583074043838760834507)
                  ·
                    rfl

theorem cell22_2494006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2494006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494006 prefixEnd_2494006 := by exact prefixLift 2494006
  have htrace : WordTrace (prefixWord ++ tailWord_2494006) baseStart_2494006 baseEnd_2494006 := by
    simpa [prefixWord, tailWord_2494006, baseEnd_2494006] using wordTrace_append hprefix tailTrace_2494006
  have hstable : (prefixWord ++ tailWord_2494006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494006).length < 2 ^ (prefixWord ++ tailWord_2494006).sum := by decide
  have hdescent : baseEnd_2494006 < baseStart_2494006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494017 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 6]
def baseStart_2494017 : Nat := 118140960795 + 2494017 * 2 ^ 59
def prefixEnd_2494017 : Nat := 4983230072969 + 3 ^ 40 * 2494017 * 2
def baseEnd_2494017 : Nat := 284584329218771973492829

theorem tailTrace_2494017 : CollatzResearch.WordTrace tailWord_2494017 prefixEnd_2494017 284584329218771973492829 := by
  unfold tailWord_2494017
  simp only [CollatzResearch.WordTrace]
  refine ⟨90964273005609828037560305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60642848670406552025040203 90964273005609828037560305)
  ·
    refine ⟨68223204754207371028170229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90964273005609828037560305 68223204754207371028170229)
    ·
      refine ⟨6395925445706941033890959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68223204754207371028170229 6395925445706941033890959)
      ·
        refine ⟨9593888168560411550836439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395925445706941033890959 9593888168560411550836439)
        ·
          refine ⟨14390832252840617326254659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9593888168560411550836439 14390832252840617326254659)
          ·
            refine ⟨21586248379260925989381989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14390832252840617326254659 21586248379260925989381989)
            ·
              refine ⟨4047421571111423623009123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21586248379260925989381989 4047421571111423623009123)
              ·
                refine ⟨6071132356667135434513685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047421571111423623009123 6071132356667135434513685)
                ·
                  refine ⟨284584329218771973492829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6071132356667135434513685 284584329218771973492829)
                  ·
                    rfl

theorem cell22_2494017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_2494017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494017 prefixEnd_2494017 := by exact prefixLift 2494017
  have htrace : WordTrace (prefixWord ++ tailWord_2494017) baseStart_2494017 baseEnd_2494017 := by
    simpa [prefixWord, tailWord_2494017, baseEnd_2494017] using wordTrace_append hprefix tailTrace_2494017
  have hstable : (prefixWord ++ tailWord_2494017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494017).length < 2 ^ (prefixWord ++ tailWord_2494017).sum := by decide
  have hdescent : baseEnd_2494017 < baseStart_2494017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494075 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_2494075 : Nat := 118140960795 + 2494075 * 2 ^ 59
def prefixEnd_2494075 : Nat := 4983230072969 + 3 ^ 40 * 2494075 * 2
def baseEnd_2494075 : Nat := 853772842241623102528309

theorem tailTrace_2494075 : CollatzResearch.WordTrace tailWord_2494075 prefixEnd_2494075 853772842241623102528309 := by
  unfold tailWord_2494075
  simp only [CollatzResearch.WordTrace]
  refine ⟨90966388439399703943171679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60644258959599802628781119 90966388439399703943171679)
  ·
    refine ⟨136449582659099555914757519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90966388439399703943171679 136449582659099555914757519)
    ·
      refine ⟨204674373988649333872136279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136449582659099555914757519 204674373988649333872136279)
      ·
        refine ⟨307011560982974000808204419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204674373988649333872136279 307011560982974000808204419)
        ·
          refine ⟨460517341474461001212306629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307011560982974000808204419 460517341474461001212306629)
          ·
            refine ⟨86347001526461437727307493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 460517341474461001212306629 86347001526461437727307493)
            ·
              refine ⟨16190062786211519573870155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86347001526461437727307493 16190062786211519573870155)
              ·
                refine ⟨24285094179317279360805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16190062786211519573870155 24285094179317279360805233)
                ·
                  refine ⟨18213820634487959520603925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24285094179317279360805233 18213820634487959520603925)
                  ·
                    refine ⟨853772842241623102528309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18213820634487959520603925 853772842241623102528309)
                    ·
                      rfl

theorem cell22_2494075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_2494075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494075 prefixEnd_2494075 := by exact prefixLift 2494075
  have htrace : WordTrace (prefixWord ++ tailWord_2494075) baseStart_2494075 baseEnd_2494075 := by
    simpa [prefixWord, tailWord_2494075, baseEnd_2494075] using wordTrace_append hprefix tailTrace_2494075
  have hstable : (prefixWord ++ tailWord_2494075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494075).length < 2 ^ (prefixWord ++ tailWord_2494075).sum := by decide
  have hdescent : baseEnd_2494075 < baseStart_2494075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2494105 : Nat := 118140960795 + 2494105 * 2 ^ 59
def prefixEnd_2494105 : Nat := 4983230072969 + 3 ^ 40 * 2494105 * 2
def baseEnd_2494105 : Nat := 853783111854713024278217

theorem tailTrace_2494105 : CollatzResearch.WordTrace tailWord_2494105 prefixEnd_2494105 853783111854713024278217 := by
  unfold tailWord_2494105
  simp only [CollatzResearch.WordTrace]
  refine ⟨90967482629291019066763769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60644988419527346044509179 90967482629291019066763769)
  ·
    refine ⟨68225611971968264300072827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90967482629291019066763769 68225611971968264300072827)
    ·
      refine ⟨102338417957952396450109241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68225611971968264300072827 102338417957952396450109241)
      ·
        refine ⟨76753813468464297337581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102338417957952396450109241 76753813468464297337581931)
        ·
          refine ⟨115130720202696446006372897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76753813468464297337581931 115130720202696446006372897)
          ·
            refine ⟨86348040152022334504779673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115130720202696446006372897 86348040152022334504779673)
            ·
              refine ⟨64761030114016750878584755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86348040152022334504779673 64761030114016750878584755)
              ·
                refine ⟨97141545171025126317877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64761030114016750878584755 97141545171025126317877133)
                ·
                  refine ⟨36428079439134422369203925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97141545171025126317877133 36428079439134422369203925)
                  ·
                    refine ⟨853783111854713024278217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36428079439134422369203925 853783111854713024278217)
                    ·
                      rfl

theorem cell22_2494105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2494105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494105 prefixEnd_2494105 := by exact prefixLift 2494105
  have htrace : WordTrace (prefixWord ++ tailWord_2494105) baseStart_2494105 baseEnd_2494105 := by
    simpa [prefixWord, tailWord_2494105, baseEnd_2494105] using wordTrace_append hprefix tailTrace_2494105
  have hstable : (prefixWord ++ tailWord_2494105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494105).length < 2 ^ (prefixWord ++ tailWord_2494105).sum := by decide
  have hdescent : baseEnd_2494105 < baseStart_2494105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494137 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2494137 : Nat := 118140960795 + 2494137 * 2 ^ 59
def prefixEnd_2494137 : Nat := 4983230072969 + 3 ^ 40 * 2494137 * 2
def baseEnd_2494137 : Nat := 853794066108675607478119

theorem tailTrace_2494137 : CollatzResearch.WordTrace tailWord_2494137 prefixEnd_2494137 853794066108675607478119 := by
  unfold tailWord_2494137
  simp only [CollatzResearch.WordTrace]
  refine ⟨90968649765175088531928665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60645766510116725687952443 90968649765175088531928665)
  ·
    refine ⟨68226487323881316398946499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90968649765175088531928665 68226487323881316398946499)
    ·
      refine ⟨102339730985821974598419749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68226487323881316398946499 102339730985821974598419749)
      ·
        refine ⟨19188699559841620237203703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102339730985821974598419749 19188699559841620237203703)
        ·
          refine ⟨28783049339762430355805555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19188699559841620237203703 28783049339762430355805555)
          ·
            refine ⟨43174574009643645533708333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28783049339762430355805555 43174574009643645533708333)
            ·
              refine ⟨16190465253616367075140625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43174574009643645533708333 16190465253616367075140625)
              ·
                refine ⟨12142848940212275306355469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16190465253616367075140625 12142848940212275306355469)
                ·
                  refine ⟨4553568352579603239883301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12142848940212275306355469 4553568352579603239883301)
                  ·
                    refine ⟨853794066108675607478119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553568352579603239883301 853794066108675607478119)
                    ·
                      rfl

theorem cell22_2494137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2494137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494137 prefixEnd_2494137 := by exact prefixLift 2494137
  have htrace : WordTrace (prefixWord ++ tailWord_2494137) baseStart_2494137 baseEnd_2494137 := by
    simpa [prefixWord, tailWord_2494137, baseEnd_2494137] using wordTrace_append hprefix tailTrace_2494137
  have hstable : (prefixWord ++ tailWord_2494137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494137).length < 2 ^ (prefixWord ++ tailWord_2494137).sum := by decide
  have hdescent : baseEnd_2494137 < baseStart_2494137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494152 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_2494152 : Nat := 118140960795 + 2494152 * 2 ^ 59
def prefixEnd_2494152 : Nat := 4983230072969 + 3 ^ 40 * 2494152 * 2
def baseEnd_2494152 : Nat := 284599733638406856117691

theorem tailTrace_2494152 : CollatzResearch.WordTrace tailWord_2494152 prefixEnd_2494152 284599733638406856117691 := by
  unfold tailWord_2494152
  simp only [CollatzResearch.WordTrace]
  refine ⟨45484598430060373046862355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60646131240080497395816473 45484598430060373046862355)
  ·
    refine ⟨68226897645090559570293533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45484598430060373046862355 68226897645090559570293533)
    ·
      refine ⟨25585086616908959838860075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68226897645090559570293533 25585086616908959838860075)
      ·
        refine ⟨38377629925363439758290113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25585086616908959838860075 38377629925363439758290113)
        ·
          refine ⟨28783222444022579818717585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38377629925363439758290113 28783222444022579818717585)
          ·
            refine ⟨21587416833016934864038189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28783222444022579818717585 21587416833016934864038189)
            ·
              refine ⟨8095281312381350574014321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21587416833016934864038189 8095281312381350574014321)
              ·
                refine ⟨6071460984286012930510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8095281312381350574014321 6071460984286012930510741)
                ·
                  refine ⟨284599733638406856117691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6071460984286012930510741 284599733638406856117691)
                  ·
                    rfl

theorem cell22_2494152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_2494152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494152 prefixEnd_2494152 := by exact prefixLift 2494152
  have htrace : WordTrace (prefixWord ++ tailWord_2494152) baseStart_2494152 baseEnd_2494152 := by
    simpa [prefixWord, tailWord_2494152, baseEnd_2494152] using wordTrace_append hprefix tailTrace_2494152
  have hstable : (prefixWord ++ tailWord_2494152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494152).length < 2 ^ (prefixWord ++ tailWord_2494152).sum := by decide
  have hdescent : baseEnd_2494152 < baseStart_2494152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494167 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2494167 : Nat := 118140960795 + 2494167 * 2 ^ 59
def prefixEnd_2494167 : Nat := 4983230072969 + 3 ^ 40 * 2494167 * 2
def baseEnd_2494167 : Nat := 853804335721765529228027

theorem tailTrace_2494167 : CollatzResearch.WordTrace tailWord_2494167 prefixEnd_2494167 853804335721765529228027 := by
  unfold tailWord_2494167
  simp only [CollatzResearch.WordTrace]
  refine ⟨90969743955066403655520755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60646495970044269103680503 90969743955066403655520755)
  ·
    refine ⟨136454615932599605483281133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90969743955066403655520755 136454615932599605483281133)
    ·
      refine ⟨51170480974724852056230425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136454615932599605483281133 51170480974724852056230425)
      ·
        refine ⟨38377860731043639042172819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51170480974724852056230425 38377860731043639042172819)
        ·
          refine ⟨57566791096565458563259229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38377860731043639042172819 57566791096565458563259229)
          ·
            refine ⟨21587546661212046961222211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57566791096565458563259229 21587546661212046961222211)
            ·
              refine ⟨32381319991818070441833317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21587546661212046961222211 32381319991818070441833317)
              ·
                refine ⟨6071497498465888207843747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32381319991818070441833317 6071497498465888207843747)
                ·
                  refine ⟨9107246247698832311765621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071497498465888207843747 9107246247698832311765621)
                  ·
                    refine ⟨853804335721765529228027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9107246247698832311765621 853804335721765529228027)
                    ·
                      rfl

theorem cell22_2494167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2494167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494167 prefixEnd_2494167 := by exact prefixLift 2494167
  have htrace : WordTrace (prefixWord ++ tailWord_2494167) baseStart_2494167 baseEnd_2494167 := by
    simpa [prefixWord, tailWord_2494167, baseEnd_2494167] using wordTrace_append hprefix tailTrace_2494167
  have hstable : (prefixWord ++ tailWord_2494167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494167).length < 2 ^ (prefixWord ++ tailWord_2494167).sum := by decide
  have hdescent : baseEnd_2494167 < baseStart_2494167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494169 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 4]
def baseStart_2494169 : Nat := 118140960795 + 2494169 * 2 ^ 59
def prefixEnd_2494169 : Nat := 4983230072969 + 3 ^ 40 * 2494169 * 2
def baseEnd_2494169 : Nat := 284601673454212730226007

theorem tailTrace_2494169 : CollatzResearch.WordTrace tailWord_2494169 prefixEnd_2494169 284601673454212730226007 := by
  unfold tailWord_2494169
  simp only [CollatzResearch.WordTrace]
  refine ⟨90969816901059157997093561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60646544600706105331395707 90969816901059157997093561)
  ·
    refine ⟨68227362675794368497820171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90969816901059157997093561 68227362675794368497820171)
    ·
      refine ⟨102341044013691552746730257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68227362675794368497820171 102341044013691552746730257)
      ·
        refine ⟨76755783010268664560047693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102341044013691552746730257 76755783010268664560047693)
        ·
          refine ⟨28783418628850749210017885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76755783010268664560047693 28783418628850749210017885)
          ·
            refine ⟨10793781985819030953756707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28783418628850749210017885 10793781985819030953756707)
            ·
              refine ⟨16190672978728546430635061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10793781985819030953756707 16190672978728546430635061)
              ·
                refine ⟨1517875591755801227872037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16190672978728546430635061 1517875591755801227872037)
                ·
                  refine ⟨284601673454212730226007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517875591755801227872037 284601673454212730226007)
                  ·
                    rfl

theorem cell22_2494169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_2494169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494169 prefixEnd_2494169 := by exact prefixLift 2494169
  have htrace : WordTrace (prefixWord ++ tailWord_2494169) baseStart_2494169 baseEnd_2494169 := by
    simpa [prefixWord, tailWord_2494169, baseEnd_2494169] using wordTrace_append hprefix tailTrace_2494169
  have hstable : (prefixWord ++ tailWord_2494169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494169).length < 2 ^ (prefixWord ++ tailWord_2494169).sum := by decide
  have hdescent : baseEnd_2494169 < baseStart_2494169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494306 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2494306 : Nat := 118140960795 + 2494306 * 2 ^ 59
def prefixEnd_2494306 : Nat := 4983230072969 + 3 ^ 40 * 2494306 * 2
def baseEnd_2494306 : Nat := 853851918262415500002601

theorem tailTrace_2494306 : CollatzResearch.WordTrace tailWord_2494306 prefixEnd_2494306 853851918262415500002601 := by
  unfold tailWord_2494306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22743703425390707598707693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60649875801041886929887181 22743703425390707598707693)
  ·
    refine ⟨8528888784521515349515385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22743703425390707598707693 8528888784521515349515385)
    ·
      refine ⟨6396666588391136512136539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8528888784521515349515385 6396666588391136512136539)
      ·
        refine ⟨9594999882586704768204809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6396666588391136512136539 9594999882586704768204809)
        ·
          refine ⟨7196249911940028576153607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9594999882586704768204809 7196249911940028576153607)
          ·
            refine ⟨10794374867910042864230411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7196249911940028576153607 10794374867910042864230411)
            ·
              refine ⟨16191562301865064296345617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10794374867910042864230411 16191562301865064296345617)
              ·
                refine ⟨12143671726398798222259213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16191562301865064296345617 12143671726398798222259213)
                ·
                  refine ⟨4553876897399549333347205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12143671726398798222259213 4553876897399549333347205)
                  ·
                    refine ⟨853851918262415500002601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553876897399549333347205 853851918262415500002601)
                    ·
                      rfl

theorem cell22_2494306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2494306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494306 prefixEnd_2494306 := by exact prefixLift 2494306
  have htrace : WordTrace (prefixWord ++ tailWord_2494306) baseStart_2494306 baseEnd_2494306 := by
    simpa [prefixWord, tailWord_2494306, baseEnd_2494306] using wordTrace_append hprefix tailTrace_2494306
  have hstable : (prefixWord ++ tailWord_2494306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494306).length < 2 ^ (prefixWord ++ tailWord_2494306).sum := by decide
  have hdescent : baseEnd_2494306 < baseStart_2494306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494319 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 8, 3]
def baseStart_2494319 : Nat := 118140960795 + 2494319 * 2 ^ 59
def prefixEnd_2494319 : Nat := 4983230072969 + 3 ^ 40 * 2494319 * 2
def baseEnd_2494319 : Nat := 853856368428087799427561

theorem tailTrace_2494319 : CollatzResearch.WordTrace tailWord_2494319 prefixEnd_2494319 853856368428087799427561 := by
  unfold tailWord_2494319
  simp only [CollatzResearch.WordTrace]
  refine ⟨90975287850515733615054011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60650191900343822410036007 90975287850515733615054011)
  ·
    refine ⟨136462931775773600422581017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90975287850515733615054011 136462931775773600422581017)
    ·
      refine ⟨102347198831830200316935763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136462931775773600422581017 102347198831830200316935763)
      ·
        refine ⟨153520798247745300475403645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102347198831830200316935763 153520798247745300475403645)
        ·
          refine ⟨57570299342904487678276367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153520798247745300475403645 57570299342904487678276367)
          ·
            refine ⟨86355449014356731517414551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57570299342904487678276367 86355449014356731517414551)
            ·
              refine ⟨129533173521535097276121827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86355449014356731517414551 129533173521535097276121827)
              ·
                refine ⟨194299760282302645914182741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129533173521535097276121827 194299760282302645914182741)
                ·
                  refine ⟨2276950315808234131806829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 194299760282302645914182741 2276950315808234131806829)
                  ·
                    refine ⟨853856368428087799427561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276950315808234131806829 853856368428087799427561)
                    ·
                      rfl

theorem cell22_2494319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_2494319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494319 prefixEnd_2494319 := by exact prefixLift 2494319
  have htrace : WordTrace (prefixWord ++ tailWord_2494319) baseStart_2494319 baseEnd_2494319 := by
    simpa [prefixWord, tailWord_2494319, baseEnd_2494319] using wordTrace_append hprefix tailTrace_2494319
  have hstable : (prefixWord ++ tailWord_2494319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494319).length < 2 ^ (prefixWord ++ tailWord_2494319).sum := by decide
  have hdescent : baseEnd_2494319 < baseStart_2494319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494370 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2494370 : Nat := 118140960795 + 2494370 * 2 ^ 59
def prefixEnd_2494370 : Nat := 4983230072969 + 3 ^ 40 * 2494370 * 2
def baseEnd_2494370 : Nat := 853873826770340666402405

theorem tailTrace_2494370 : CollatzResearch.WordTrace tailWord_2494370 prefixEnd_2494370 853873826770340666402405 := by
  unfold tailWord_2494370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22744286993332742331290141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60651431982220646216773709 22744286993332742331290141)
  ·
    refine ⟨8529107622499778374233803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22744286993332742331290141 8529107622499778374233803)
    ·
      refine ⟨12793661433749667561350705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529107622499778374233803 12793661433749667561350705)
      ·
        refine ⟨9595246075312250671013029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12793661433749667561350705 9595246075312250671013029)
        ·
          refine ⟨1799108639121047000814943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9595246075312250671013029 1799108639121047000814943)
          ·
            refine ⟨2698662958681570501222415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799108639121047000814943 2698662958681570501222415)
            ·
              refine ⟨4047994438022355751833623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698662958681570501222415 4047994438022355751833623)
              ·
                refine ⟨6071991657033533627750435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047994438022355751833623 6071991657033533627750435)
                ·
                  refine ⟨9107987485550300441625653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071991657033533627750435 9107987485550300441625653)
                  ·
                    refine ⟨853873826770340666402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9107987485550300441625653 853873826770340666402405)
                    ·
                      rfl

theorem cell22_2494370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2494370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494370 prefixEnd_2494370 := by exact prefixLift 2494370
  have htrace : WordTrace (prefixWord ++ tailWord_2494370) baseStart_2494370 baseEnd_2494370 := by
    simpa [prefixWord, tailWord_2494370, baseEnd_2494370] using wordTrace_append hprefix tailTrace_2494370
  have hstable : (prefixWord ++ tailWord_2494370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494370).length < 2 ^ (prefixWord ++ tailWord_2494370).sum := by decide
  have hdescent : baseEnd_2494370 < baseStart_2494370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494415 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 1, 3]
def baseStart_2494415 : Nat := 118140960795 + 2494415 * 2 ^ 59
def prefixEnd_2494415 : Nat := 4983230072969 + 3 ^ 40 * 2494415 * 2
def baseEnd_2494415 : Nat := 853889231189975549027267

theorem tailTrace_2494415 : CollatzResearch.WordTrace tailWord_2494415 prefixEnd_2494415 853889231189975549027267 := by
  unfold tailWord_2494415
  simp only [CollatzResearch.WordTrace]
  refine ⟨90978789258167942010548699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60652526172111961340365799 90978789258167942010548699)
  ·
    refine ⟨136468183887251913015823049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90978789258167942010548699 136468183887251913015823049)
    ·
      refine ⟨102351137915438934761867287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136468183887251913015823049 102351137915438934761867287)
      ·
        refine ⟨153526706873158402142800931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102351137915438934761867287 153526706873158402142800931)
        ·
          refine ⟨230290060309737603214201397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153526706873158402142800931 230290060309737603214201397)
          ·
            refine ⟨21589693154037900301331381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230290060309737603214201397 21589693154037900301331381)
            ·
              refine ⟨2024033733191053153249817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21589693154037900301331381 2024033733191053153249817)
              ·
                refine ⟨1518025299893289864937363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024033733191053153249817 1518025299893289864937363)
                ·
                  refine ⟨2277037949839934797406045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518025299893289864937363 2277037949839934797406045)
                  ·
                    refine ⟨853889231189975549027267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277037949839934797406045 853889231189975549027267)
                    ·
                      rfl

theorem cell22_2494415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_2494415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494415 prefixEnd_2494415 := by exact prefixLift 2494415
  have htrace : WordTrace (prefixWord ++ tailWord_2494415) baseStart_2494415 baseEnd_2494415 := by
    simpa [prefixWord, tailWord_2494415, baseEnd_2494415] using wordTrace_append hprefix tailTrace_2494415
  have hstable : (prefixWord ++ tailWord_2494415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494415).length < 2 ^ (prefixWord ++ tailWord_2494415).sum := by decide
  have hdescent : baseEnd_2494415 < baseStart_2494415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494477 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2494477 : Nat := 118140960795 + 2494477 * 2 ^ 59
def prefixEnd_2494477 : Nat := 4983230072969 + 3 ^ 40 * 2494477 * 2
def baseEnd_2494477 : Nat := 853910455057028053977077

theorem tailTrace_2494477 : CollatzResearch.WordTrace tailWord_2494477 prefixEnd_2494477 853910455057028053977077 := by
  unfold tailWord_2494477
  simp only [CollatzResearch.WordTrace]
  refine ⟨90981050583943326599305685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60654033722628884399537123 90981050583943326599305685)
  ·
    refine ⟨2132368373061171717171227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90981050583943326599305685 2132368373061171717171227)
    ·
      refine ⟨3198552559591757575756841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132368373061171717171227 3198552559591757575756841)
      ·
        refine ⟨2398914419693818181817631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198552559591757575756841 2398914419693818181817631)
        ·
          refine ⟨3598371629540727272726447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398914419693818181817631 3598371629540727272726447)
          ·
            refine ⟨5397557444311090909089671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598371629540727272726447 5397557444311090909089671)
            ·
              refine ⟨8096336166466636363634507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397557444311090909089671 8096336166466636363634507)
              ·
                refine ⟨12144504249699954545451761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096336166466636363634507 12144504249699954545451761)
                ·
                  refine ⟨9108378187274965909088821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12144504249699954545451761 9108378187274965909088821)
                  ·
                    refine ⟨853910455057028053977077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9108378187274965909088821 853910455057028053977077)
                    ·
                      rfl

theorem cell22_2494477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2494477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494477 prefixEnd_2494477 := by exact prefixLift 2494477
  have htrace : WordTrace (prefixWord ++ tailWord_2494477) baseStart_2494477 baseEnd_2494477 := by
    simpa [prefixWord, tailWord_2494477, baseEnd_2494477] using wordTrace_append hprefix tailTrace_2494477
  have hstable : (prefixWord ++ tailWord_2494477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494477).length < 2 ^ (prefixWord ++ tailWord_2494477).sum := by decide
  have hdescent : baseEnd_2494477 < baseStart_2494477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494488 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_2494488 : Nat := 118140960795 + 2494488 * 2 ^ 59
def prefixEnd_2494488 : Nat := 4983230072969 + 3 ^ 40 * 2494488 * 2
def baseEnd_2494488 : Nat := 853914220581827691952043

theorem tailTrace_2494488 : CollatzResearch.WordTrace tailWord_2494488 prefixEnd_2494488 853914220581827691952043 := by
  unfold tailWord_2494488
  simp only [CollatzResearch.WordTrace]
  refine ⟨45490725893451737738978059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60654301191268983651970745 45490725893451737738978059)
  ·
    refine ⟨68236088840177606608467089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45490725893451737738978059 68236088840177606608467089)
    ·
      refine ⟨51177066630133204956350317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68236088840177606608467089 51177066630133204956350317)
      ·
        refine ⟨19191399986299951858631369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51177066630133204956350317 19191399986299951858631369)
        ·
          refine ⟨14393549989724963893973527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19191399986299951858631369 14393549989724963893973527)
          ·
            refine ⟨21590324984587445840960291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14393549989724963893973527 21590324984587445840960291)
            ·
              refine ⟨32385487476881168761440437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21590324984587445840960291 32385487476881168761440437)
              ·
                refine ⟨3036139450957609571385041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32385487476881168761440437 3036139450957609571385041)
                ·
                  refine ⟨2277104588218207178538781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036139450957609571385041 2277104588218207178538781)
                  ·
                    refine ⟨853914220581827691952043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277104588218207178538781 853914220581827691952043)
                    ·
                      rfl

theorem cell22_2494488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_2494488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494488 prefixEnd_2494488 := by exact prefixLift 2494488
  have htrace : WordTrace (prefixWord ++ tailWord_2494488) baseStart_2494488 baseEnd_2494488 := by
    simpa [prefixWord, tailWord_2494488, baseEnd_2494488] using wordTrace_append hprefix tailTrace_2494488
  have hstable : (prefixWord ++ tailWord_2494488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494488).length < 2 ^ (prefixWord ++ tailWord_2494488).sum := by decide
  have hdescent : baseEnd_2494488 < baseStart_2494488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494623 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_2494623 : Nat := 118140960795 + 2494623 * 2 ^ 59
def prefixEnd_2494623 : Nat := 4983230072969 + 3 ^ 40 * 2494623 * 2
def baseEnd_2494623 : Nat := 853960433840732339826629

theorem tailTrace_2494623 : CollatzResearch.WordTrace tailWord_2494623 prefixEnd_2494623 853960433840732339826629 := by
  unfold tailWord_2494623
  simp only [CollatzResearch.WordTrace]
  refine ⟨90986375641414393534120523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60657583760942929022747015 90986375641414393534120523)
  ·
    refine ⟨136479563462121590301180785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90986375641414393534120523 136479563462121590301180785)
    ·
      refine ⟨102359672596591192725885589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136479563462121590301180785 102359672596591192725885589)
      ·
        refine ⟨4798109652965212159025887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102359672596591192725885589 4798109652965212159025887)
        ·
          refine ⟨7197164479447818238538831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798109652965212159025887 7197164479447818238538831)
          ·
            refine ⟨10795746719171727357808247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197164479447818238538831 10795746719171727357808247)
            ·
              refine ⟨16193620078757591036712371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10795746719171727357808247 16193620078757591036712371)
              ·
                refine ⟨24290430118136386555068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16193620078757591036712371 24290430118136386555068557)
                ·
                  refine ⟨9108911294301144958150709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24290430118136386555068557 9108911294301144958150709)
                  ·
                    refine ⟨853960433840732339826629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9108911294301144958150709 853960433840732339826629)
                    ·
                      rfl

theorem cell22_2494623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_2494623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494623 prefixEnd_2494623 := by exact prefixLift 2494623
  have htrace : WordTrace (prefixWord ++ tailWord_2494623) baseStart_2494623 baseEnd_2494623 := by
    simpa [prefixWord, tailWord_2494623, baseEnd_2494623] using wordTrace_append hprefix tailTrace_2494623
  have hstable : (prefixWord ++ tailWord_2494623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494623).length < 2 ^ (prefixWord ++ tailWord_2494623).sum := by decide
  have hdescent : baseEnd_2494623 < baseStart_2494623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494657 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2494657 : Nat := 118140960795 + 2494657 * 2 ^ 59
def prefixEnd_2494657 : Nat := 4983230072969 + 3 ^ 40 * 2494657 * 2
def baseEnd_2494657 : Nat := 853972072735567584476525

theorem tailTrace_2494657 : CollatzResearch.WordTrace tailWord_2494657 prefixEnd_2494657 853972072735567584476525 := by
  unfold tailWord_2494657
  simp only [CollatzResearch.WordTrace]
  refine ⟨90987615723291217340858225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60658410482194144893905483 90987615723291217340858225)
  ·
    refine ⟨68240711792468413005643669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90987615723291217340858225 68240711792468413005643669)
    ·
      refine ⟨3198783365271956859639547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68240711792468413005643669 3198783365271956859639547)
      ·
        refine ⟨4798175047907935289459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3198783365271956859639547 4798175047907935289459321)
        ·
          refine ⟨3598631285930951467094491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4798175047907935289459321 3598631285930951467094491)
          ·
            refine ⟨5397946928896427200641737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598631285930951467094491 5397946928896427200641737)
            ·
              refine ⟨4048460196672320400481303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5397946928896427200641737 4048460196672320400481303)
              ·
                refine ⟨6072690295008480600721955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048460196672320400481303 6072690295008480600721955)
                ·
                  refine ⟨9109035442512720901082933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072690295008480600721955 9109035442512720901082933)
                  ·
                    refine ⟨853972072735567584476525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9109035442512720901082933 853972072735567584476525)
                    ·
                      rfl

theorem cell22_2494657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2494657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494657 prefixEnd_2494657 := by exact prefixLift 2494657
  have htrace : WordTrace (prefixWord ++ tailWord_2494657) baseStart_2494657 baseEnd_2494657 := by
    simpa [prefixWord, tailWord_2494657, baseEnd_2494657] using wordTrace_append hprefix tailTrace_2494657
  have hstable : (prefixWord ++ tailWord_2494657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494657).length < 2 ^ (prefixWord ++ tailWord_2494657).sum := by decide
  have hdescent : baseEnd_2494657 < baseStart_2494657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494670 : List Nat := [4, 1, 1, 1, 4, 2, 3, 6]
def baseStart_2494670 : Nat := 118140960795 + 2494670 * 2 ^ 59
def prefixEnd_2494670 : Nat := 4983230072969 + 3 ^ 40 * 2494670 * 2
def baseEnd_2494670 : Nat := 94886280322359987100165

theorem tailTrace_2494670 : CollatzResearch.WordTrace tailWord_2494670 prefixEnd_2494670 94886280322359987100165 := by
  unfold tailWord_2494670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373511234030515070135183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60658726581496080374054309 11373511234030515070135183)
  ·
    refine ⟨17060266851045772605202775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373511234030515070135183 17060266851045772605202775)
    ·
      refine ⟨25590400276568658907804163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17060266851045772605202775 25590400276568658907804163)
      ·
        refine ⟨38385600414852988361706245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25590400276568658907804163 38385600414852988361706245)
        ·
          refine ⟨7197300077784935317819921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38385600414852988361706245 7197300077784935317819921)
          ·
            refine ⟨5397975058338701488364941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7197300077784935317819921 5397975058338701488364941)
            ·
              refine ⟨2024240646877013058136853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5397975058338701488364941 2024240646877013058136853)
              ·
                refine ⟨94886280322359987100165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2024240646877013058136853 94886280322359987100165)
                ·
                  rfl

theorem cell22_2494670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_2494670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494670 prefixEnd_2494670 := by exact prefixLift 2494670
  have htrace : WordTrace (prefixWord ++ tailWord_2494670) baseStart_2494670 baseEnd_2494670 := by
    simpa [prefixWord, tailWord_2494670, baseEnd_2494670] using wordTrace_append hprefix tailTrace_2494670
  have hstable : (prefixWord ++ tailWord_2494670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494670).length < 2 ^ (prefixWord ++ tailWord_2494670).sum := by decide
  have hdescent : baseEnd_2494670 < baseStart_2494670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494691 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 2, 3]
def baseStart_2494691 : Nat := 118140960795 + 2494691 * 2 ^ 59
def prefixEnd_2494691 : Nat := 4983230072969 + 3 ^ 40 * 2494691 * 2
def baseEnd_2494691 : Nat := 853983711630402829126421

theorem tailTrace_2494691 : CollatzResearch.WordTrace tailWord_2494691 prefixEnd_2494691 853983711630402829126421 := by
  unfold tailWord_2494691
  simp only [CollatzResearch.WordTrace]
  refine ⟨90988855805168041147595927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60659237203445360765063951 90988855805168041147595927)
  ·
    refine ⟨136483283707752061721393891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90988855805168041147595927 136483283707752061721393891)
    ·
      refine ⟨204724925561628092582090837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136483283707752061721393891 204724925561628092582090837)
      ·
        refine ⟨2399120221425329209946377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 204724925561628092582090837 2399120221425329209946377)
        ·
          refine ⟨1799340166068996907459783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2399120221425329209946377 1799340166068996907459783)
          ·
            refine ⟨2699010249103495361189675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799340166068996907459783 2699010249103495361189675)
            ·
              refine ⟨4048515373655243041784513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699010249103495361189675 4048515373655243041784513)
              ·
                refine ⟨3036386530241432281338385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048515373655243041784513 3036386530241432281338385)
                ·
                  refine ⟨2277289897681074211003789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036386530241432281338385 2277289897681074211003789)
                  ·
                    refine ⟨853983711630402829126421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277289897681074211003789 853983711630402829126421)
                    ·
                      rfl

theorem cell22_2494691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 3].length) (baseStart_2494691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494691 prefixEnd_2494691 := by exact prefixLift 2494691
  have htrace : WordTrace (prefixWord ++ tailWord_2494691) baseStart_2494691 baseEnd_2494691 := by
    simpa [prefixWord, tailWord_2494691, baseEnd_2494691] using wordTrace_append hprefix tailTrace_2494691
  have hstable : (prefixWord ++ tailWord_2494691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494691).length < 2 ^ (prefixWord ++ tailWord_2494691).sum := by decide
  have hdescent : baseEnd_2494691 < baseStart_2494691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494698 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_2494698 : Nat := 118140960795 + 2494698 * 2 ^ 59
def prefixEnd_2494698 : Nat := 4983230072969 + 3 ^ 40 * 2494698 * 2
def baseEnd_2494698 : Nat := 284662035957819048067133

theorem tailTrace_2494698 : CollatzResearch.WordTrace tailWord_2494698 prefixEnd_2494698 284662035957819048067133 := by
  unfold tailWord_2494698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747277779035670335775187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60659407410761787562067165 22747277779035670335775187)
  ·
    refine ⟨34120916668553505503662781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22747277779035670335775187 34120916668553505503662781)
    ·
      refine ⟨12795343750707564563873543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34120916668553505503662781 12795343750707564563873543)
      ·
        refine ⟨19193015626061346845810315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795343750707564563873543 19193015626061346845810315)
        ·
          refine ⟨28789523439092020268715473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19193015626061346845810315 28789523439092020268715473)
          ·
            refine ⟨21592142579319015201536605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28789523439092020268715473 21592142579319015201536605)
            ·
              refine ⟨8097053467244630700576227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21592142579319015201536605 8097053467244630700576227)
              ·
                refine ⟨12145580200866946050864341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8097053467244630700576227 12145580200866946050864341)
                ·
                  refine ⟨284662035957819048067133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12145580200866946050864341 284662035957819048067133)
                  ·
                    rfl

theorem cell22_2494698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_2494698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494698 prefixEnd_2494698 := by exact prefixLift 2494698
  have htrace : WordTrace (prefixWord ++ tailWord_2494698) baseStart_2494698 baseEnd_2494698 := by
    simpa [prefixWord, tailWord_2494698, baseEnd_2494698] using wordTrace_append hprefix tailTrace_2494698
  have hstable : (prefixWord ++ tailWord_2494698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494698).length < 2 ^ (prefixWord ++ tailWord_2494698).sum := by decide
  have hdescent : baseEnd_2494698 < baseStart_2494698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494766 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_2494766 : Nat := 118140960795 + 2494766 * 2 ^ 59
def prefixEnd_2494766 : Nat := 4983230072969 + 3 ^ 40 * 2494766 * 2
def baseEnd_2494766 : Nat := 284669795221042544500397

theorem tailTrace_2494766 : CollatzResearch.WordTrace tailWord_2494766 prefixEnd_2494766 284669795221042544500397 := by
  unfold tailWord_2494766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373948909987041119572019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60661060853264219304384101 11373948909987041119572019)
  ·
    refine ⟨17060923364980561679358029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373948909987041119572019 17060923364980561679358029)
    ·
      refine ⟨6397846261867710629759261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17060923364980561679358029 6397846261867710629759261)
      ·
        refine ⟨2399192348200391486159723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6397846261867710629759261 2399192348200391486159723)
        ·
          refine ⟨3598788522300587229239585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399192348200391486159723 3598788522300587229239585)
          ·
            refine ⟨2699091391725440421929689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598788522300587229239585 2699091391725440421929689)
            ·
              refine ⟨2024318543794080316447267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699091391725440421929689 2024318543794080316447267)
              ·
                refine ⟨3036477815691120474670901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024318543794080316447267 3036477815691120474670901)
                ·
                  refine ⟨284669795221042544500397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036477815691120474670901 284669795221042544500397)
                  ·
                    rfl

theorem cell22_2494766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_2494766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494766 prefixEnd_2494766 := by exact prefixLift 2494766
  have htrace : WordTrace (prefixWord ++ tailWord_2494766) baseStart_2494766 baseEnd_2494766 := by
    simpa [prefixWord, tailWord_2494766, baseEnd_2494766] using wordTrace_append hprefix tailTrace_2494766
  have hstable : (prefixWord ++ tailWord_2494766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494766).length < 2 ^ (prefixWord ++ tailWord_2494766).sum := by decide
  have hdescent : baseEnd_2494766 < baseStart_2494766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494805 : List Nat := [1, 3, 2, 2, 5, 9]
def baseStart_2494805 : Nat := 118140960795 + 2494805 * 2 ^ 59
def prefixEnd_2494805 : Nat := 4983230072969 + 3 ^ 40 * 2494805 * 2
def baseEnd_2494805 : Nat := 10543490569878327552791

theorem tailTrace_2494805 : CollatzResearch.WordTrace tailWord_2494805 prefixEnd_2494805 10543490569878327552791 := by
  unfold tailWord_2494805
  simp only [CollatzResearch.WordTrace]
  refine ⟨90993013726755038617245869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60662009151170025744830579 90993013726755038617245869)
  ·
    refine ⟨34122380147533139481467201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90993013726755038617245869 34122380147533139481467201)
    ·
      refine ⟨25591785110649854611100401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34122380147533139481467201 25591785110649854611100401)
      ·
        refine ⟨19193838832987390958325301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25591785110649854611100401 19193838832987390958325301)
        ·
          refine ⟨1799422390592567902342997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19193838832987390958325301 1799422390592567902342997)
          ·
            refine ⟨10543490569878327552791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1799422390592567902342997 10543490569878327552791)
            ·
              rfl

theorem cell22_2494805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 9].length) (baseStart_2494805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494805 prefixEnd_2494805 := by exact prefixLift 2494805
  have htrace : WordTrace (prefixWord ++ tailWord_2494805) baseStart_2494805 baseEnd_2494805 := by
    simpa [prefixWord, tailWord_2494805, baseEnd_2494805] using wordTrace_append hprefix tailTrace_2494805
  have hstable : (prefixWord ++ tailWord_2494805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494805).length < 2 ^ (prefixWord ++ tailWord_2494805).sum := by decide
  have hdescent : baseEnd_2494805 < baseStart_2494805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494833 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 9]
def baseStart_2494833 : Nat := 118140960795 + 2494833 * 2 ^ 59
def prefixEnd_2494833 : Nat := 4983230072969 + 3 ^ 40 * 2494833 * 2
def baseEnd_2494833 : Nat := 284677440377453930691995

theorem tailTrace_2494833 : CollatzResearch.WordTrace tailWord_2494833 prefixEnd_2494833 284677440377453930691995 := by
  unfold tailWord_2494833
  simp only [CollatzResearch.WordTrace]
  refine ⟨90994034970653599399265153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60662689980435732932843435 90994034970653599399265153)
  ·
    refine ⟨68245526227990199549448865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90994034970653599399265153 68245526227990199549448865)
    ·
      refine ⟨51184144670992649662086649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68245526227990199549448865 51184144670992649662086649)
      ·
        refine ⟨38388108503244487246564987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51184144670992649662086649 38388108503244487246564987)
        ·
          refine ⟨57582162754866730869847481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38388108503244487246564987 57582162754866730869847481)
          ·
            refine ⟨43186622066150048152385611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57582162754866730869847481 43186622066150048152385611)
            ·
              refine ⟨64779933099225072228578417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43186622066150048152385611 64779933099225072228578417)
              ·
                refine ⟨48584949824418804171433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64779933099225072228578417 48584949824418804171433813)
                ·
                  refine ⟨284677440377453930691995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48584949824418804171433813 284677440377453930691995)
                  ·
                    rfl

theorem cell22_2494833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_2494833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494833 prefixEnd_2494833 := by exact prefixLift 2494833
  have htrace : WordTrace (prefixWord ++ tailWord_2494833) baseStart_2494833 baseEnd_2494833 := by
    simpa [prefixWord, tailWord_2494833, baseEnd_2494833] using wordTrace_append hprefix tailTrace_2494833
  have hstable : (prefixWord ++ tailWord_2494833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494833).length < 2 ^ (prefixWord ++ tailWord_2494833).sum := by decide
  have hdescent : baseEnd_2494833 < baseStart_2494833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494837 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2494837 : Nat := 118140960795 + 2494837 * 2 ^ 59
def prefixEnd_2494837 : Nat := 4983230072969 + 3 ^ 40 * 2494837 * 2
def baseEnd_2494837 : Nat := 854033690414107114975973

theorem tailTrace_2494837 : CollatzResearch.WordTrace tailWord_2494837 prefixEnd_2494837 854033690414107114975973 := by
  unfold tailWord_2494837
  simp only [CollatzResearch.WordTrace]
  refine ⟨90994180862639108082410765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60662787241759405388273843 90994180862639108082410765)
  ·
    refine ⟨34122817823489665530904037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90994180862639108082410765 34122817823489665530904037)
    ·
      refine ⟨6398028341904312287044507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34122817823489665530904037 6398028341904312287044507)
      ·
        refine ⟨9597042512856468430566761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398028341904312287044507 9597042512856468430566761)
        ·
          refine ⟨7197781884642351322925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9597042512856468430566761 7197781884642351322925071)
          ·
            refine ⟨10796672826963526984387607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197781884642351322925071 10796672826963526984387607)
            ·
              refine ⟨16195009240445290476581411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796672826963526984387607 16195009240445290476581411)
              ·
                refine ⟨24292513860667935714872117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16195009240445290476581411 24292513860667935714872117)
                ·
                  refine ⟨2277423174437618973269261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24292513860667935714872117 2277423174437618973269261)
                  ·
                    refine ⟨854033690414107114975973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277423174437618973269261 854033690414107114975973)
                    ·
                      rfl

theorem cell22_2494837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2494837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494837 prefixEnd_2494837 := by exact prefixLift 2494837
  have htrace : WordTrace (prefixWord ++ tailWord_2494837) baseStart_2494837 baseEnd_2494837 := by
    simpa [prefixWord, tailWord_2494837, baseEnd_2494837] using wordTrace_append hprefix tailTrace_2494837
  have hstable : (prefixWord ++ tailWord_2494837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494837).length < 2 ^ (prefixWord ++ tailWord_2494837).sum := by decide
  have hdescent : baseEnd_2494837 < baseStart_2494837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494897 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2494897 : Nat := 118140960795 + 2494897 * 2 ^ 59
def prefixEnd_2494897 : Nat := 4983230072969 + 3 ^ 40 * 2494897 * 2
def baseEnd_2494897 : Nat := 854054229640286958475789

theorem tailTrace_2494897 : CollatzResearch.WordTrace tailWord_2494897 prefixEnd_2494897 854054229640286958475789 := by
  unfold tailWord_2494897
  simp only [CollatzResearch.WordTrace]
  refine ⟨90996369242421738329594945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60664246161614492219729963 90996369242421738329594945)
  ·
    refine ⟨68247276931816303747196209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90996369242421738329594945 68247276931816303747196209)
    ·
      refine ⟨51185457698862227810397157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68247276931816303747196209 51185457698862227810397157)
      ·
        refine ⟨9597273318536667714449467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51185457698862227810397157 9597273318536667714449467)
        ·
          refine ⟨14395909977805001571674201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9597273318536667714449467 14395909977805001571674201)
          ·
            refine ⟨10796932483353751178755651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14395909977805001571674201 10796932483353751178755651)
            ·
              refine ⟨16195398725030626768133477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796932483353751178755651 16195398725030626768133477)
              ·
                refine ⟨3036637260943242519025027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16195398725030626768133477 3036637260943242519025027)
                ·
                  refine ⟨4554955891414863778537541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036637260943242519025027 4554955891414863778537541)
                  ·
                    refine ⟨854054229640286958475789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4554955891414863778537541 854054229640286958475789)
                    ·
                      rfl

theorem cell22_2494897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2494897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494897 prefixEnd_2494897 := by exact prefixLift 2494897
  have htrace : WordTrace (prefixWord ++ tailWord_2494897) baseStart_2494897 baseEnd_2494897 := by
    simpa [prefixWord, tailWord_2494897, baseEnd_2494897] using wordTrace_append hprefix tailTrace_2494897
  have hstable : (prefixWord ++ tailWord_2494897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494897).length < 2 ^ (prefixWord ++ tailWord_2494897).sum := by decide
  have hdescent : baseEnd_2494897 < baseStart_2494897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494927 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 2, 3]
def baseStart_2494927 : Nat := 118140960795 + 2494927 * 2 ^ 59
def prefixEnd_2494927 : Nat := 4983230072969 + 3 ^ 40 * 2494927 * 2
def baseEnd_2494927 : Nat := 854064499253376880225697

theorem tailTrace_2494927 : CollatzResearch.WordTrace tailWord_2494927 prefixEnd_2494927 854064499253376880225697 := by
  unfold tailWord_2494927
  simp only [CollatzResearch.WordTrace]
  refine ⟨90997463432313053453187035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60664975621542035635458023 90997463432313053453187035)
  ·
    refine ⟨136496195148469580179780553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90997463432313053453187035 136496195148469580179780553)
    ·
      refine ⟨102372146361352185134835415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136496195148469580179780553 102372146361352185134835415)
      ·
        refine ⟨153558219542028277702253123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102372146361352185134835415 153558219542028277702253123)
        ·
          refine ⟨230337329313042416553379685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153558219542028277702253123 230337329313042416553379685)
          ·
            refine ⟨43188249246195453103758691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230337329313042416553379685 43188249246195453103758691)
            ·
              refine ⟨64782373869293179655638037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43188249246195453103758691 64782373869293179655638037)
              ·
                refine ⟨3036673775123117796358033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64782373869293179655638037 3036673775123117796358033)
                ·
                  refine ⟨2277505331342338347268525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036673775123117796358033 2277505331342338347268525)
                  ·
                    refine ⟨854064499253376880225697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277505331342338347268525 854064499253376880225697)
                    ·
                      rfl

theorem cell22_2494927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_2494927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494927 prefixEnd_2494927 := by exact prefixLift 2494927
  have htrace : WordTrace (prefixWord ++ tailWord_2494927) baseStart_2494927 baseEnd_2494927 := by
    simpa [prefixWord, tailWord_2494927, baseEnd_2494927] using wordTrace_append hprefix tailTrace_2494927
  have hstable : (prefixWord ++ tailWord_2494927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494927).length < 2 ^ (prefixWord ++ tailWord_2494927).sum := by decide
  have hdescent : baseEnd_2494927 < baseStart_2494927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494957 : List Nat := [1, 5, 1, 3, 1, 1, 2, 8]
def baseStart_2494957 : Nat := 118140960795 + 2494957 * 2 ^ 59
def prefixEnd_2494957 : Nat := 4983230072969 + 3 ^ 40 * 2494957 * 2
def baseEnd_2494957 : Nat := 94897196540718533552845

theorem tailTrace_2494957 : CollatzResearch.WordTrace tailWord_2494957 prefixEnd_2494957 94897196540718533552845 := by
  unfold tailWord_2494957
  simp only [CollatzResearch.WordTrace]
  refine ⟨90998557622204368576779125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60665705081469579051186083 90998557622204368576779125)
  ·
    refine ⟨8531114777081659554073043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90998557622204368576779125 8531114777081659554073043)
    ·
      refine ⟨12796672165622489331109565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8531114777081659554073043 12796672165622489331109565)
      ·
        refine ⟨4798752062108433499166087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12796672165622489331109565 4798752062108433499166087)
        ·
          refine ⟨7198128093162650248749131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798752062108433499166087 7198128093162650248749131)
          ·
            refine ⟨10797192139743975373123697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198128093162650248749131 10797192139743975373123697)
            ·
              refine ⟨8097894104807981529842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10797192139743975373123697 8097894104807981529842773)
              ·
                refine ⟨94897196540718533552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8097894104807981529842773 94897196540718533552845)
                ·
                  rfl

theorem cell22_2494957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 8].length) (baseStart_2494957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494957 prefixEnd_2494957 := by exact prefixLift 2494957
  have htrace : WordTrace (prefixWord ++ tailWord_2494957) baseStart_2494957 baseEnd_2494957 := by
    simpa [prefixWord, tailWord_2494957, baseEnd_2494957] using wordTrace_append hprefix tailTrace_2494957
  have hstable : (prefixWord ++ tailWord_2494957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494957).length < 2 ^ (prefixWord ++ tailWord_2494957).sum := by decide
  have hdescent : baseEnd_2494957 < baseStart_2494957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494978 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2494978 : Nat := 118140960795 + 2494978 * 2 ^ 59
def prefixEnd_2494978 : Nat := 4983230072969 + 3 ^ 40 * 2494978 * 2
def baseEnd_2494978 : Nat := 854081957595629747200541

theorem tailTrace_2494978 : CollatzResearch.WordTrace tailWord_2494978 prefixEnd_2494978 854081957595629747200541 := by
  unfold tailWord_2494978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749830888782072290823397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60666215703418859442195725 22749830888782072290823397)
  ·
    refine ⟨4265593291646638554529387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22749830888782072290823397 4265593291646638554529387)
    ·
      refine ⟨6398389937469957831794081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265593291646638554529387 6398389937469957831794081)
      ·
        refine ⟨4798792453102468373845561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6398389937469957831794081 4798792453102468373845561)
        ·
          refine ⟨3599094339826851280384171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4798792453102468373845561 3599094339826851280384171)
          ·
            refine ⟨5398641509740276920576257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599094339826851280384171 5398641509740276920576257)
            ·
              refine ⟨4048981132305207690432193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398641509740276920576257 4048981132305207690432193)
              ·
                refine ⟨3036735849228905767824145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048981132305207690432193 3036735849228905767824145)
                ·
                  refine ⟨2277551886921679325868109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036735849228905767824145 2277551886921679325868109)
                  ·
                    refine ⟨854081957595629747200541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277551886921679325868109 854081957595629747200541)
                    ·
                      rfl

theorem cell22_2494978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2494978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2494978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2494978 prefixEnd_2494978 := by exact prefixLift 2494978
  have htrace : WordTrace (prefixWord ++ tailWord_2494978) baseStart_2494978 baseEnd_2494978 := by
    simpa [prefixWord, tailWord_2494978, baseEnd_2494978] using wordTrace_append hprefix tailTrace_2494978
  have hstable : (prefixWord ++ tailWord_2494978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494978).length < 2 ^ (prefixWord ++ tailWord_2494978).sum := by decide
  have hdescent : baseEnd_2494978 < baseStart_2494978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495002 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_2495002 : Nat := 118140960795 + 2495002 * 2 ^ 59
def prefixEnd_2495002 : Nat := 4983230072969 + 3 ^ 40 * 2495002 * 2
def baseEnd_2495002 : Nat := 284696724428700561533489

theorem tailTrace_2495002 : CollatzResearch.WordTrace tailWord_2495002 prefixEnd_2495002 284696724428700561533489 := by
  unfold tailWord_2495002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22750049726760335315541815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60666799271360894174778173 22750049726760335315541815)
  ·
    refine ⟨34125074590140502973312723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22750049726760335315541815 34125074590140502973312723)
    ·
      refine ⟨51187611885210754459969085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34125074590140502973312723 51187611885210754459969085)
      ·
        refine ⟨19195354456954032922488407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51187611885210754459969085 19195354456954032922488407)
        ·
          refine ⟨28793031685431049383732611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19195354456954032922488407 28793031685431049383732611)
          ·
            refine ⟨43189547528146574075598917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28793031685431049383732611 43189547528146574075598917)
            ·
              refine ⟨8098040161527482639174797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43189547528146574075598917 8098040161527482639174797)
              ·
                refine ⟨3036765060572805989690549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8098040161527482639174797 3036765060572805989690549)
                ·
                  refine ⟨284696724428700561533489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036765060572805989690549 284696724428700561533489)
                  ·
                    rfl

theorem cell22_2495002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_2495002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495002 prefixEnd_2495002 := by exact prefixLift 2495002
  have htrace : WordTrace (prefixWord ++ tailWord_2495002) baseStart_2495002 baseEnd_2495002 := by
    simpa [prefixWord, tailWord_2495002, baseEnd_2495002] using wordTrace_append hprefix tailTrace_2495002
  have hstable : (prefixWord ++ tailWord_2495002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495002).length < 2 ^ (prefixWord ++ tailWord_2495002).sum := by decide
  have hdescent : baseEnd_2495002 < baseStart_2495002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495047 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 6]
def baseStart_2495047 : Nat := 118140960795 + 2495047 * 2 ^ 59
def prefixEnd_2495047 : Nat := 4983230072969 + 3 ^ 40 * 2495047 * 2
def baseEnd_2495047 : Nat := 284701859235245522408443

theorem tailTrace_2495047 : CollatzResearch.WordTrace tailWord_2495047 prefixEnd_2495047 284701859235245522408443 := by
  unfold tailWord_2495047
  simp only [CollatzResearch.WordTrace]
  refine ⟨91001840191878313947555395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60667893461252209298370263 91001840191878313947555395)
  ·
    refine ⟨136502760287817470921333093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91001840191878313947555395 136502760287817470921333093)
    ·
      refine ⟨25594267553965775797749955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136502760287817470921333093 25594267553965775797749955)
      ·
        refine ⟨38391401330948663696624933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25594267553965775797749955 38391401330948663696624933)
        ·
          refine ⟨7198387749552874443117175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38391401330948663696624933 7198387749552874443117175)
          ·
            refine ⟨10797581624329311664675763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198387749552874443117175 10797581624329311664675763)
            ·
              refine ⟨16196372436493967497013645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10797581624329311664675763 16196372436493967497013645)
              ·
                refine ⟨6073639663685237811380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16196372436493967497013645 6073639663685237811380117)
                ·
                  refine ⟨284701859235245522408443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6073639663685237811380117 284701859235245522408443)
                  ·
                    rfl

theorem cell22_2495047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_2495047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495047 prefixEnd_2495047 := by exact prefixLift 2495047
  have htrace : WordTrace (prefixWord ++ tailWord_2495047) baseStart_2495047 baseEnd_2495047 := by
    simpa [prefixWord, tailWord_2495047, baseEnd_2495047] using wordTrace_append hprefix tailTrace_2495047
  have hstable : (prefixWord ++ tailWord_2495047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495047).length < 2 ^ (prefixWord ++ tailWord_2495047).sum := by decide
  have hdescent : baseEnd_2495047 < baseStart_2495047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495141 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_2495141 : Nat := 118140960795 + 2495141 * 2 ^ 59
def prefixEnd_2495141 : Nat := 4983230072969 + 3 ^ 40 * 2495141 * 2
def baseEnd_2495141 : Nat := 854137755826751655375041

theorem tailTrace_2495141 : CollatzResearch.WordTrace tailWord_2495141 prefixEnd_2495141 854137755826751655375041 := by
  unfold tailWord_2495141
  simp only [CollatzResearch.WordTrace]
  refine ⟨91005268653537768001477277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60670179102358512000984851 91005268653537768001477277)
  ·
    refine ⟨34126975745076663000553979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91005268653537768001477277 34126975745076663000553979)
    ·
      refine ⟨51190463617614994500830969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34126975745076663000553979 51190463617614994500830969)
      ·
        refine ⟨38392847713211245875623227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51190463617614994500830969 38392847713211245875623227)
        ·
          refine ⟨57589271569816868813434841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38392847713211245875623227 57589271569816868813434841)
          ·
            refine ⟨43191953677362651610076131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57589271569816868813434841 43191953677362651610076131)
            ·
              refine ⟨64787930516043977415114197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43191953677362651610076131 64787930516043977415114197)
              ·
                refine ⟨1518467121469780720666739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64787930516043977415114197 1518467121469780720666739)
                ·
                  refine ⟨2277700682204671081000109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518467121469780720666739 2277700682204671081000109)
                  ·
                    refine ⟨854137755826751655375041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277700682204671081000109 854137755826751655375041)
                    ·
                      rfl

theorem cell22_2495141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_2495141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495141 prefixEnd_2495141 := by exact prefixLift 2495141
  have htrace : WordTrace (prefixWord ++ tailWord_2495141) baseStart_2495141 baseEnd_2495141 := by
    simpa [prefixWord, tailWord_2495141, baseEnd_2495141] using wordTrace_append hprefix tailTrace_2495141
  have hstable : (prefixWord ++ tailWord_2495141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495141).length < 2 ^ (prefixWord ++ tailWord_2495141).sum := by decide
  have hdescent : baseEnd_2495141 < baseStart_2495141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495152 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_2495152 : Nat := 118140960795 + 2495152 * 2 ^ 59
def prefixEnd_2495152 : Nat := 4983230072969 + 3 ^ 40 * 2495152 * 2
def baseEnd_2495152 : Nat := 854141521351551293350007

theorem tailTrace_2495152 : CollatzResearch.WordTrace tailWord_2495152 prefixEnd_2495152 854141521351551293350007 := by
  unfold tailWord_2495152
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502834928248958440063855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60670446570998611253418473 45502834928248958440063855)
  ·
    refine ⟨68254252392373437660095783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45502834928248958440063855 68254252392373437660095783)
    ·
      refine ⟨102381378588560156490143675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68254252392373437660095783 102381378588560156490143675)
      ·
        refine ⟨153572067882840234735215513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102381378588560156490143675 153572067882840234735215513)
        ·
          refine ⟨115179050912130176051411635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153572067882840234735215513 115179050912130176051411635)
          ·
            refine ⟨172768576368195264077117453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115179050912130176051411635 172768576368195264077117453)
            ·
              refine ⟨64788216138073224028919045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172768576368195264077117453 64788216138073224028919045)
              ·
                refine ⟨12147790525888729505422321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64788216138073224028919045 12147790525888729505422321)
                ·
                  refine ⟨9110842894416547129066741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12147790525888729505422321 9110842894416547129066741)
                  ·
                    refine ⟨854141521351551293350007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9110842894416547129066741 854141521351551293350007)
                    ·
                      rfl

theorem cell22_2495152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_2495152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495152 prefixEnd_2495152 := by exact prefixLift 2495152
  have htrace : WordTrace (prefixWord ++ tailWord_2495152) baseStart_2495152 baseEnd_2495152 := by
    simpa [prefixWord, tailWord_2495152, baseEnd_2495152] using wordTrace_append hprefix tailTrace_2495152
  have hstable : (prefixWord ++ tailWord_2495152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495152).length < 2 ^ (prefixWord ++ tailWord_2495152).sum := by decide
  have hdescent : baseEnd_2495152 < baseStart_2495152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495201 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2495201 : Nat := 118140960795 + 2495201 * 2 ^ 59
def prefixEnd_2495201 : Nat := 4983230072969 + 3 ^ 40 * 2495201 * 2
def baseEnd_2495201 : Nat := 854158295052931498874857

theorem tailTrace_2495201 : CollatzResearch.WordTrace tailWord_2495201 prefixEnd_2495201 854158295052931498874857 := by
  unfold tailWord_2495201
  simp only [CollatzResearch.WordTrace]
  refine ⟨91007457033320398248661457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60671638022213598832440971 91007457033320398248661457)
  ·
    refine ⟨68255592774990298686496093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91007457033320398248661457 68255592774990298686496093)
    ·
      refine ⟨25595847290621362007436035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68255592774990298686496093 25595847290621362007436035)
      ·
        refine ⟨38393770935932043011154053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25595847290621362007436035 38393770935932043011154053)
        ·
          refine ⟨7198832050487258064591385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38393770935932043011154053 7198832050487258064591385)
          ·
            refine ⟨5399124037865443548443539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198832050487258064591385 5399124037865443548443539)
            ·
              refine ⟨8098686056798165322665309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399124037865443548443539 8098686056798165322665309)
              ·
                refine ⟨3037007271299311995999491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8098686056798165322665309 3037007271299311995999491)
                ·
                  refine ⟨4555510906948967993999237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037007271299311995999491 4555510906948967993999237)
                  ·
                    refine ⟨854158295052931498874857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555510906948967993999237 854158295052931498874857)
                    ·
                      rfl

theorem cell22_2495201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2495201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495201 prefixEnd_2495201 := by exact prefixLift 2495201
  have htrace : WordTrace (prefixWord ++ tailWord_2495201) baseStart_2495201 baseEnd_2495201 := by
    simpa [prefixWord, tailWord_2495201, baseEnd_2495201] using wordTrace_append hprefix tailTrace_2495201
  have hstable : (prefixWord ++ tailWord_2495201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495201).length < 2 ^ (prefixWord ++ tailWord_2495201).sum := by decide
  have hdescent : baseEnd_2495201 < baseStart_2495201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495336 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2495336 : Nat := 118140960795 + 2495336 * 2 ^ 59
def prefixEnd_2495336 : Nat := 4983230072969 + 3 ^ 40 * 2495336 * 2
def baseEnd_2495336 : Nat := 854204508311836146749443

theorem tailTrace_2495336 : CollatzResearch.WordTrace tailWord_2495336 prefixEnd_2495336 854204508311836146749443 := by
  unfold tailWord_2495336
  simp only [CollatzResearch.WordTrace]
  refine ⟨45506190443915658152412931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60674920591887544203217241 45506190443915658152412931)
  ·
    refine ⟨68259285665873487228619397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45506190443915658152412931 68259285665873487228619397)
    ·
      refine ⟨12798616062351278855366137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68259285665873487228619397 12798616062351278855366137)
      ·
        refine ⟨9598962046763459141524603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12798616062351278855366137 9598962046763459141524603)
        ·
          refine ⟨14398443070145188712286905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9598962046763459141524603 14398443070145188712286905)
          ·
            refine ⟨10798832302608891534215179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14398443070145188712286905 10798832302608891534215179)
            ·
              refine ⟨16198248453913337301322769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798832302608891534215179 16198248453913337301322769)
              ·
                refine ⟨12148686340435002975992077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16198248453913337301322769 12148686340435002975992077)
                ·
                  refine ⟨4555757377663126115997029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12148686340435002975992077 4555757377663126115997029)
                  ·
                    refine ⟨854204508311836146749443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555757377663126115997029 854204508311836146749443)
                    ·
                      rfl

theorem cell22_2495336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2495336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495336 prefixEnd_2495336 := by exact prefixLift 2495336
  have htrace : WordTrace (prefixWord ++ tailWord_2495336) baseStart_2495336 baseEnd_2495336 := by
    simpa [prefixWord, tailWord_2495336, baseEnd_2495336] using wordTrace_append hprefix tailTrace_2495336
  have hstable : (prefixWord ++ tailWord_2495336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495336).length < 2 ^ (prefixWord ++ tailWord_2495336).sum := by decide
  have hdescent : baseEnd_2495336 < baseStart_2495336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495368 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_2495368 : Nat := 118140960795 + 2495368 * 2 ^ 59
def prefixEnd_2495368 : Nat := 4983230072969 + 3 ^ 40 * 2495368 * 2
def baseEnd_2495368 : Nat := 284738487521932909983115

theorem tailTrace_2495368 : CollatzResearch.WordTrace tailWord_2495368 prefixEnd_2495368 284738487521932909983115 := by
  unfold tailWord_2495368
  simp only [CollatzResearch.WordTrace]
  refine ⟨45506774011857692884995379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60675698682476923846660505 45506774011857692884995379)
  ·
    refine ⟨68260161017786539327493069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45506774011857692884995379 68260161017786539327493069)
    ·
      refine ⟨25597560381669952247809901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68260161017786539327493069 25597560381669952247809901)
      ·
        refine ⟨9599085143126232092928713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25597560381669952247809901 9599085143126232092928713)
        ·
          refine ⟨7199313857344674069696535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9599085143126232092928713 7199313857344674069696535)
          ·
            refine ⟨10798970786017011104544803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7199313857344674069696535 10798970786017011104544803)
            ·
              refine ⟨16198456179025516656817205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798970786017011104544803 16198456179025516656817205)
              ·
                refine ⟨1518605266783642186576613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16198456179025516656817205 1518605266783642186576613)
                ·
                  refine ⟨284738487521932909983115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518605266783642186576613 284738487521932909983115)
                  ·
                    rfl

theorem cell22_2495368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_2495368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495368 prefixEnd_2495368 := by exact prefixLift 2495368
  have htrace : WordTrace (prefixWord ++ tailWord_2495368) baseStart_2495368 baseEnd_2495368 := by
    simpa [prefixWord, tailWord_2495368, baseEnd_2495368] using wordTrace_append hprefix tailTrace_2495368
  have hstable : (prefixWord ++ tailWord_2495368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495368).length < 2 ^ (prefixWord ++ tailWord_2495368).sum := by decide
  have hdescent : baseEnd_2495368 < baseStart_2495368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495370 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2495370 : Nat := 118140960795 + 2495370 * 2 ^ 59
def prefixEnd_2495370 : Nat := 4983230072969 + 3 ^ 40 * 2495370 * 2
def baseEnd_2495370 : Nat := 854216147206671391399339

theorem tailTrace_2495370 : CollatzResearch.WordTrace tailWord_2495370 prefixEnd_2495370 854216147206671391399339 := by
  unfold tailWord_2495370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22753405242427035027890891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60675747313138760074375709 22753405242427035027890891)
  ·
    refine ⟨34130107863640552541836337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22753405242427035027890891 34130107863640552541836337)
    ·
      refine ⟨25597580897730414406377253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34130107863640552541836337 25597580897730414406377253)
      ·
        refine ⟨4799546418324452701195735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25597580897730414406377253 4799546418324452701195735)
        ·
          refine ⟨7199319627486679051793603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799546418324452701195735 7199319627486679051793603)
          ·
            refine ⟨10798979441230018577690405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7199319627486679051793603 10798979441230018577690405)
            ·
              refine ⟨2024808645230628483316951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10798979441230018577690405 2024808645230628483316951)
              ·
                refine ⟨3037212967845942724975427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024808645230628483316951 3037212967845942724975427)
                ·
                  refine ⟨4555819451768914087463141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037212967845942724975427 4555819451768914087463141)
                  ·
                    refine ⟨854216147206671391399339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555819451768914087463141 854216147206671391399339)
                    ·
                      rfl

theorem cell22_2495370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2495370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495370 prefixEnd_2495370 := by exact prefixLift 2495370
  have htrace : WordTrace (prefixWord ++ tailWord_2495370) baseStart_2495370 baseEnd_2495370 := by
    simpa [prefixWord, tailWord_2495370, baseEnd_2495370] using wordTrace_append hprefix tailTrace_2495370
  have hstable : (prefixWord ++ tailWord_2495370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495370).length < 2 ^ (prefixWord ++ tailWord_2495370).sum := by decide
  have hdescent : baseEnd_2495370 < baseStart_2495370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495411 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 5, 3]
def baseStart_2495411 : Nat := 118140960795 + 2495411 * 2 ^ 59
def prefixEnd_2495411 : Nat := 4983230072969 + 3 ^ 40 * 2495411 * 2
def baseEnd_2495411 : Nat := 854230182344560951124213

theorem tailTrace_2495411 : CollatzResearch.WordTrace tailWord_2495411 prefixEnd_2495411 854230182344560951124213 := by
  unfold tailWord_2495411
  simp only [CollatzResearch.WordTrace]
  refine ⟨91015116362559604113806087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60676744241706402742537391 91015116362559604113806087)
  ·
    refine ⟨136522674543839406170709131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91015116362559604113806087 136522674543839406170709131)
    ·
      refine ⟨204784011815759109256063697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136522674543839406170709131 204784011815759109256063697)
      ·
        refine ⟨153588008861819331942047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204784011815759109256063697 153588008861819331942047773)
        ·
          refine ⟨57595503323182249478267915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153588008861819331942047773 57595503323182249478267915)
          ·
            refine ⟨86393254984773374217401873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57595503323182249478267915 86393254984773374217401873)
            ·
              refine ⟨64794941238580030663051405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86393254984773374217401873 64794941238580030663051405)
              ·
                refine ⟨24298102964467511498644277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64794941238580030663051405 24298102964467511498644277)
                ·
                  refine ⟨2277947152918829202997901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24298102964467511498644277 2277947152918829202997901)
                  ·
                    refine ⟨854230182344560951124213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277947152918829202997901 854230182344560951124213)
                    ·
                      rfl

theorem cell22_2495411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].length) (baseStart_2495411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495411 prefixEnd_2495411 := by exact prefixLift 2495411
  have htrace : WordTrace (prefixWord ++ tailWord_2495411) baseStart_2495411 baseEnd_2495411 := by
    simpa [prefixWord, tailWord_2495411, baseEnd_2495411] using wordTrace_append hprefix tailTrace_2495411
  have hstable : (prefixWord ++ tailWord_2495411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495411).length < 2 ^ (prefixWord ++ tailWord_2495411).sum := by decide
  have hdescent : baseEnd_2495411 < baseStart_2495411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495441 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 5]
def baseStart_2495441 : Nat := 118140960795 + 2495441 * 2 ^ 59
def prefixEnd_2495441 : Nat := 4983230072969 + 3 ^ 40 * 2495441 * 2
def baseEnd_2495441 : Nat := 284746817319216957624707

theorem tailTrace_2495441 : CollatzResearch.WordTrace tailWord_2495441 prefixEnd_2495441 284746817319216957624707 := by
  unfold tailWord_2495441
  simp only [CollatzResearch.WordTrace]
  refine ⟨91016210552450919237398177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60677473701633946158265451 91016210552450919237398177)
  ·
    refine ⟨68262157914338189428048633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91016210552450919237398177 68262157914338189428048633)
    ·
      refine ⟨51196618435753642071036475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68262157914338189428048633 51196618435753642071036475)
      ·
        refine ⟨76794927653630463106554713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51196618435753642071036475 76794927653630463106554713)
        ·
          refine ⟨57596195740222847329916035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76794927653630463106554713 57596195740222847329916035)
          ·
            refine ⟨86394293610334270994874053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57596195740222847329916035 86394293610334270994874053)
            ·
              refine ⟨16198930051937675811538885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86394293610334270994874053 16198930051937675811538885)
              ·
                refine ⟨3037299384738314214663541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16198930051937675811538885 3037299384738314214663541)
                ·
                  refine ⟨284746817319216957624707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3037299384738314214663541 284746817319216957624707)
                  ·
                    rfl

theorem cell22_2495441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_2495441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495441 prefixEnd_2495441 := by exact prefixLift 2495441
  have htrace : WordTrace (prefixWord ++ tailWord_2495441) baseStart_2495441 baseEnd_2495441 := by
    simpa [prefixWord, tailWord_2495441, baseEnd_2495441] using wordTrace_append hprefix tailTrace_2495441
  have hstable : (prefixWord ++ tailWord_2495441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495441).length < 2 ^ (prefixWord ++ tailWord_2495441).sum := by decide
  have hdescent : baseEnd_2495441 < baseStart_2495441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495520 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_2495520 : Nat := 118140960795 + 2495520 * 2 ^ 59
def prefixEnd_2495520 : Nat := 4983230072969 + 3 ^ 40 * 2495520 * 2
def baseEnd_2495520 : Nat := 284755831757373666716293

theorem tailTrace_2495520 : CollatzResearch.WordTrace tailWord_2495520 prefixEnd_2495520 284755831757373666716293 := by
  unfold tailWord_2495520
  simp only [CollatzResearch.WordTrace]
  refine ⟨45509545959582357864762007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60679394612776477153016009 45509545959582357864762007)
  ·
    refine ⟨68264318939373536797143011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45509545959582357864762007 68264318939373536797143011)
    ·
      refine ⟨102396478409060305195714517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68264318939373536797143011 102396478409060305195714517)
      ·
        refine ⟨2399917462712350903024559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102396478409060305195714517 2399917462712350903024559)
        ·
          refine ⟨3599876194068526354536839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399917462712350903024559 3599876194068526354536839)
          ·
            refine ⟨5399814291102789531805259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599876194068526354536839 5399814291102789531805259)
            ·
              refine ⟨8099721436654184297707889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399814291102789531805259 8099721436654184297707889)
              ·
                refine ⟨6074791077490638223280917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8099721436654184297707889 6074791077490638223280917)
                ·
                  refine ⟨284755831757373666716293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6074791077490638223280917 284755831757373666716293)
                  ·
                    rfl

theorem cell22_2495520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_2495520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495520 prefixEnd_2495520 := by exact prefixLift 2495520
  have htrace : WordTrace (prefixWord ++ tailWord_2495520) baseStart_2495520 baseEnd_2495520 := by
    simpa [prefixWord, tailWord_2495520, baseEnd_2495520] using wordTrace_append hprefix tailTrace_2495520
  have hstable : (prefixWord ++ tailWord_2495520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495520).length < 2 ^ (prefixWord ++ tailWord_2495520).sum := by decide
  have hdescent : baseEnd_2495520 < baseStart_2495520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495561 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_2495561 : Nat := 118140960795 + 2495561 * 2 ^ 59
def prefixEnd_2495561 : Nat := 4983230072969 + 3 ^ 40 * 2495561 * 2
def baseEnd_2495561 : Nat := 854281530410010559873753

theorem tailTrace_2495561 : CollatzResearch.WordTrace tailWord_2495561 prefixEnd_2495561 854281530410010559873753 := by
  unfold tailWord_2495561
  simp only [CollatzResearch.WordTrace]
  refine ⟨91020587312016179731766537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60680391541344119821177691 91020587312016179731766537)
  ·
    refine ⟨68265440484012134798824903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91020587312016179731766537 68265440484012134798824903)
    ·
      refine ⟨102398160726018202198237355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68265440484012134798824903 102398160726018202198237355)
      ·
        refine ⟨153597241089027303297356033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102398160726018202198237355 153597241089027303297356033)
        ·
          refine ⟨115197930816770477473017025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153597241089027303297356033 115197930816770477473017025)
          ·
            refine ⟨86398448112577858104762769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115197930816770477473017025 86398448112577858104762769)
            ·
              refine ⟨64798836084433393578572077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86398448112577858104762769 64798836084433393578572077)
              ·
                refine ⟨24299563531662522591964529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64798836084433393578572077 24299563531662522591964529)
                ·
                  refine ⟨18224672648746891943973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24299563531662522591964529 18224672648746891943973397)
                  ·
                    refine ⟨854281530410010559873753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18224672648746891943973397 854281530410010559873753)
                    ·
                      rfl

theorem cell22_2495561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_2495561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495561 prefixEnd_2495561 := by exact prefixLift 2495561
  have htrace : WordTrace (prefixWord ++ tailWord_2495561) baseStart_2495561 baseEnd_2495561 := by
    simpa [prefixWord, tailWord_2495561, baseEnd_2495561] using wordTrace_append hprefix tailTrace_2495561
  have hstable : (prefixWord ++ tailWord_2495561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495561).length < 2 ^ (prefixWord ++ tailWord_2495561).sum := by decide
  have hdescent : baseEnd_2495561 < baseStart_2495561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495580 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2495580 : Nat := 118140960795 + 2495580 * 2 ^ 59
def prefixEnd_2495580 : Nat := 4983230072969 + 3 ^ 40 * 2495580 * 2
def baseEnd_2495580 : Nat := 854288034498300843648695

theorem tailTrace_2495580 : CollatzResearch.WordTrace tailWord_2495580 prefixEnd_2495580 854288034498300843648695 := by
  unfold tailWord_2495580
  simp only [CollatzResearch.WordTrace]
  refine ⟨45510640149473672988354097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60680853532631563984472129 45510640149473672988354097)
  ·
    refine ⟨34132980112105254741265573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45510640149473672988354097 34132980112105254741265573)
    ·
      refine ⟨6399933771019735263987295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34132980112105254741265573 6399933771019735263987295)
      ·
        refine ⟨9599900656529602895980943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6399933771019735263987295 9599900656529602895980943)
        ·
          refine ⟨14399850984794404343971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9599900656529602895980943 14399850984794404343971415)
          ·
            refine ⟨21599776477191606515957123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14399850984794404343971415 21599776477191606515957123)
            ·
              refine ⟨32399664715787409773935685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21599776477191606515957123 32399664715787409773935685)
              ·
                refine ⟨6074937134210139332612941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32399664715787409773935685 6074937134210139332612941)
                ·
                  refine ⟨2278101425328802249729853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6074937134210139332612941 2278101425328802249729853)
                  ·
                    refine ⟨854288034498300843648695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278101425328802249729853 854288034498300843648695)
                    ·
                      rfl

theorem cell22_2495580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2495580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495580 prefixEnd_2495580 := by exact prefixLift 2495580
  have htrace : WordTrace (prefixWord ++ tailWord_2495580) baseStart_2495580 baseEnd_2495580 := by
    simpa [prefixWord, tailWord_2495580, baseEnd_2495580] using wordTrace_append hprefix tailTrace_2495580
  have hstable : (prefixWord ++ tailWord_2495580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495580).length < 2 ^ (prefixWord ++ tailWord_2495580).sum := by decide
  have hdescent : baseEnd_2495580 < baseStart_2495580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495582 : List Nat := [4, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2495582 : Nat := 118140960795 + 2495582 * 2 ^ 59
def prefixEnd_2495582 : Nat := 4983230072969 + 3 ^ 40 * 2495582 * 2
def baseEnd_2495582 : Nat := 94920968793241500566521

theorem tailTrace_2495582 : CollatzResearch.WordTrace tailWord_2495582 prefixEnd_2495582 94920968793241500566521 := by
  unfold tailWord_2495582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377669155617512539785125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60680902163293400212187333 11377669155617512539785125)
  ·
    refine ⟨2133312966678283601209711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11377669155617512539785125 2133312966678283601209711)
    ·
      refine ⟨3199969450017425401814567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133312966678283601209711 3199969450017425401814567)
      ·
        refine ⟨4799954175026138102721851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199969450017425401814567 4799954175026138102721851)
        ·
          refine ⟨7199931262539207154082777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799954175026138102721851 7199931262539207154082777)
          ·
            refine ⟨5399948446904405365562083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199931262539207154082777 5399948446904405365562083)
            ·
              refine ⟨8099922670356608048343125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399948446904405365562083 8099922670356608048343125)
              ·
                refine ⟨94920968793241500566521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8099922670356608048343125 94920968793241500566521)
                ·
                  rfl

theorem cell22_2495582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2495582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495582 prefixEnd_2495582 := by exact prefixLift 2495582
  have htrace : WordTrace (prefixWord ++ tailWord_2495582) baseStart_2495582 baseEnd_2495582 := by
    simpa [prefixWord, tailWord_2495582, baseEnd_2495582] using wordTrace_append hprefix tailTrace_2495582
  have hstable : (prefixWord ++ tailWord_2495582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495582).length < 2 ^ (prefixWord ++ tailWord_2495582).sum := by decide
  have hdescent : baseEnd_2495582 < baseStart_2495582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495623 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2495623 : Nat := 118140960795 + 2495623 * 2 ^ 59
def prefixEnd_2495623 : Nat := 4983230072969 + 3 ^ 40 * 2495623 * 2
def baseEnd_2495623 : Nat := 854302754277063064823563

theorem tailTrace_2495623 : CollatzResearch.WordTrace tailWord_2495623 prefixEnd_2495623 854302754277063064823563 := by
  unfold tailWord_2495623
  simp only [CollatzResearch.WordTrace]
  refine ⟨91022848637791564320523523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60681899091861042880349015 91022848637791564320523523)
  ·
    refine ⟨136534272956687346480785285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91022848637791564320523523 136534272956687346480785285)
    ·
      refine ⟨25600176179378877465147241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136534272956687346480785285 25600176179378877465147241)
      ·
        refine ⟨19200132134534158098860431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25600176179378877465147241 19200132134534158098860431)
        ·
          refine ⟨28800198201801237148290647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19200132134534158098860431 28800198201801237148290647)
          ·
            refine ⟨43200297302701855722435971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28800198201801237148290647 43200297302701855722435971)
            ·
              refine ⟨64800445954052783583653957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43200297302701855722435971 64800445954052783583653957)
              ·
                refine ⟨12150083616384896921935117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64800445954052783583653957 12150083616384896921935117)
                ·
                  refine ⟨4556281356144336345725669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12150083616384896921935117 4556281356144336345725669)
                  ·
                    refine ⟨854302754277063064823563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556281356144336345725669 854302754277063064823563)
                    ·
                      rfl

theorem cell22_2495623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2495623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495623 prefixEnd_2495623 := by exact prefixLift 2495623
  have htrace : WordTrace (prefixWord ++ tailWord_2495623) baseStart_2495623 baseEnd_2495623 := by
    simpa [prefixWord, tailWord_2495623, baseEnd_2495623] using wordTrace_append hprefix tailTrace_2495623
  have hstable : (prefixWord ++ tailWord_2495623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495623).length < 2 ^ (prefixWord ++ tailWord_2495623).sum := by decide
  have hdescent : baseEnd_2495623 < baseStart_2495623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
