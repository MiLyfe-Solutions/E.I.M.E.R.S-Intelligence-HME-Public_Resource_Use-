import V185TrunkScan23Chunk0137

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_816977 : List Nat := [1, 2, 2, 1, 5, 2, 2, 8]
def baseStart_816977 : Nat := 118140960795 + 816977 * 2 ^ 59
def prefixEnd_816977 : Nat := 4983230072969 + 3 ^ 40 * 816977 * 2
def baseEnd_816977 : Nat := 15537106839568715090011

theorem tailTrace_816977 : CollatzResearch.WordTrace tailWord_816977 prefixEnd_816977 15537106839568715090011 := by
  unfold tailWord_816977
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797599161239332408273185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19865066107492888272182123 29797599161239332408273185)
  ·
    refine ⟨22348199370929499306204889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29797599161239332408273185 22348199370929499306204889)
    ·
      refine ⟨16761149528197124479653667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22348199370929499306204889 16761149528197124479653667)
      ·
        refine ⟨25141724292295686719480501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16761149528197124479653667 25141724292295686719480501)
        ·
          refine ⟨2357036652402720629951297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25141724292295686719480501 2357036652402720629951297)
          ·
            refine ⟨1767777489302040472463473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357036652402720629951297 1767777489302040472463473)
            ·
              refine ⟨1325833116976530354347605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767777489302040472463473 1325833116976530354347605)
              ·
                refine ⟨15537106839568715090011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1325833116976530354347605 15537106839568715090011)
                ·
                  rfl

theorem cell23_816977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 8].length) (baseStart_816977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816977 prefixEnd_816977 := by exact prefixLift 816977
  have htrace : WordTrace (prefixWord ++ tailWord_816977) baseStart_816977 baseEnd_816977 := by
    simpa [prefixWord, tailWord_816977, baseEnd_816977] using wordTrace_append hprefix tailTrace_816977
  have hstable : (prefixWord ++ tailWord_816977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816977).length < 2 ^ (prefixWord ++ tailWord_816977).sum := by decide
  have hdescent : baseEnd_816977 < baseStart_816977 := by decide
  rcases family_descends (prefixWord ++ tailWord_816977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816981 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_816981 : Nat := 118140960795 + 816981 * 2 ^ 59
def prefixEnd_816981 : Nat := 4983230072969 + 3 ^ 40 * 816981 * 2
def baseEnd_816981 : Nat := 139834646196991097260093

theorem tailTrace_816981 : CollatzResearch.WordTrace tailWord_816981 prefixEnd_816981 139834646196991097260093 := by
  unfold tailWord_816981
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797745053224841091418797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19865163368816560727612531 29797745053224841091418797)
  ·
    refine ⟨11174154394959315409282049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29797745053224841091418797 11174154394959315409282049)
    ·
      refine ⟨8380615796219486556961537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11174154394959315409282049 8380615796219486556961537)
      ·
        refine ⟨6285461847164614917721153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8380615796219486556961537 6285461847164614917721153)
        ·
          refine ⟨4714096385373461188290865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6285461847164614917721153 4714096385373461188290865)
          ·
            refine ⟨3535572289030095891218149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714096385373461188290865 3535572289030095891218149)
            ·
              refine ⟨662919804193142979603403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3535572289030095891218149 662919804193142979603403)
              ·
                refine ⟨994379706289714469405105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662919804193142979603403 994379706289714469405105)
                ·
                  refine ⟨745784779717285852053829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994379706289714469405105 745784779717285852053829)
                  ·
                    refine ⟨139834646196991097260093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745784779717285852053829 139834646196991097260093)
                    ·
                      rfl

theorem cell23_816981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_816981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816981 prefixEnd_816981 := by exact prefixLift 816981
  have htrace : WordTrace (prefixWord ++ tailWord_816981) baseStart_816981 baseEnd_816981 := by
    simpa [prefixWord, tailWord_816981, baseEnd_816981] using wordTrace_append hprefix tailTrace_816981
  have hstable : (prefixWord ++ tailWord_816981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816981).length < 2 ^ (prefixWord ++ tailWord_816981).sum := by decide
  have hdescent : baseEnd_816981 < baseStart_816981 := by decide
  rcases family_descends (prefixWord ++ tailWord_816981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816988 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_816988 : Nat := 118140960795 + 816988 * 2 ^ 59
def prefixEnd_816988 : Nat := 4983230072969 + 3 ^ 40 * 816988 * 2
def baseEnd_816988 : Nat := 419507532955554764392747

theorem tailTrace_816988 : CollatzResearch.WordTrace tailWord_816988 prefixEnd_816988 419507532955554764392747 := by
  unfold tailWord_816988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899000182099740643461809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19865333576132987524615745 14899000182099740643461809)
  ·
    refine ⟨11174250136574805482596357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14899000182099740643461809 11174250136574805482596357)
    ·
      refine ⟨2095171900607776027986817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11174250136574805482596357 2095171900607776027986817)
      ·
        refine ⟨1571378925455832020990113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2095171900607776027986817 1571378925455832020990113)
        ·
          refine ⟨1178534194091874015742585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571378925455832020990113 1178534194091874015742585)
          ·
            refine ⟨883900645568905511806939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178534194091874015742585 883900645568905511806939)
            ·
              refine ⟨1325850968353358267710409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883900645568905511806939 1325850968353358267710409)
              ·
                refine ⟨994388226265018700782807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325850968353358267710409 994388226265018700782807)
                ·
                  refine ⟨1491582339397528051174211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994388226265018700782807 1491582339397528051174211)
                  ·
                    refine ⟨2237373509096292076761317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491582339397528051174211 2237373509096292076761317)
                    ·
                      refine ⟨419507532955554764392747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2237373509096292076761317 419507532955554764392747)
                      ·
                        rfl

theorem cell23_816988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_816988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816988 prefixEnd_816988 := by exact prefixLift 816988
  have htrace : WordTrace (prefixWord ++ tailWord_816988) baseStart_816988 baseEnd_816988 := by
    simpa [prefixWord, tailWord_816988, baseEnd_816988] using wordTrace_append hprefix tailTrace_816988
  have hstable : (prefixWord ++ tailWord_816988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816988).length < 2 ^ (prefixWord ++ tailWord_816988).sum := by decide
  have hdescent : baseEnd_816988 < baseStart_816988 := by decide
  rcases family_descends (prefixWord ++ tailWord_816988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816991 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_816991 : Nat := 118140960795 + 816991 * 2 ^ 59
def prefixEnd_816991 : Nat := 4983230072969 + 3 ^ 40 * 816991 * 2
def baseEnd_816991 : Nat := 419509073397518252655233

theorem tailTrace_816991 : CollatzResearch.WordTrace tailWord_816991 prefixEnd_816991 419509073397518252655233 := by
  unfold tailWord_816991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29798109783188612799282827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19865406522125741866188551 29798109783188612799282827)
  ·
    refine ⟨44697164674782919198924241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29798109783188612799282827 44697164674782919198924241)
    ·
      refine ⟨33522873506087189399193181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44697164674782919198924241 33522873506087189399193181)
      ·
        refine ⟨12571077564782696024697443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33522873506087189399193181 12571077564782696024697443)
        ·
          refine ⟨18856616347174044037046165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571077564782696024697443 18856616347174044037046165)
          ·
            refine ⟨883903891273783314236539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18856616347174044037046165 883903891273783314236539)
            ·
              refine ⟨1325855836910674971354809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883903891273783314236539 1325855836910674971354809)
              ·
                refine ⟨994391877683006228516107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325855836910674971354809 994391877683006228516107)
                ·
                  refine ⟨1491587816524509342774161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994391877683006228516107 1491587816524509342774161)
                  ·
                    refine ⟨1118690862393382007080621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1491587816524509342774161 1118690862393382007080621)
                    ·
                      refine ⟨419509073397518252655233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118690862393382007080621 419509073397518252655233)
                      ·
                        rfl

theorem cell23_816991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_816991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816991 prefixEnd_816991 := by exact prefixLift 816991
  have htrace : WordTrace (prefixWord ++ tailWord_816991) baseStart_816991 baseEnd_816991 := by
    simpa [prefixWord, tailWord_816991, baseEnd_816991] using wordTrace_append hprefix tailTrace_816991
  have hstable : (prefixWord ++ tailWord_816991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816991).length < 2 ^ (prefixWord ++ tailWord_816991).sum := by decide
  have hdescent : baseEnd_816991 < baseStart_816991 := by decide
  rcases family_descends (prefixWord ++ tailWord_816991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817004 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_817004 : Nat := 118140960795 + 817004 * 2 ^ 59
def prefixEnd_817004 : Nat := 4983230072969 + 3 ^ 40 * 817004 * 2
def baseEnd_817004 : Nat := 419515748646026701792673

theorem tailTrace_817004 : CollatzResearch.WordTrace tailWord_817004 prefixEnd_817004 419515748646026701792673 := by
  unfold tailWord_817004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899291966070758009753033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19865722621427677346337377 14899291966070758009753033)
  ·
    refine ⟨11174468974553068507314775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14899291966070758009753033 11174468974553068507314775)
    ·
      refine ⟨16761703461829602760972163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174468974553068507314775 16761703461829602760972163)
      ·
        refine ⟨25142555192744404141458245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16761703461829602760972163 25142555192744404141458245)
        ·
          refine ⟨4714229098639575776523421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25142555192744404141458245 4714229098639575776523421)
          ·
            refine ⟨1767835911989840916196283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4714229098639575776523421 1767835911989840916196283)
            ·
              refine ⟨2651753867984761374294425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767835911989840916196283 2651753867984761374294425)
              ·
                refine ⟨1988815400988571030720819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651753867984761374294425 1988815400988571030720819)
                ·
                  refine ⟨2983223101482856546081229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988815400988571030720819 2983223101482856546081229)
                  ·
                    refine ⟨1118708663056071204780461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983223101482856546081229 1118708663056071204780461)
                    ·
                      refine ⟨419515748646026701792673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118708663056071204780461 419515748646026701792673)
                      ·
                        rfl

theorem cell23_817004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_817004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817004 prefixEnd_817004 := by exact prefixLift 817004
  have htrace : WordTrace (prefixWord ++ tailWord_817004) baseStart_817004 baseEnd_817004 := by
    simpa [prefixWord, tailWord_817004, baseEnd_817004] using wordTrace_append hprefix tailTrace_817004
  have hstable : (prefixWord ++ tailWord_817004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817004).length < 2 ^ (prefixWord ++ tailWord_817004).sum := by decide
  have hdescent : baseEnd_817004 < baseStart_817004 := by decide
  rcases family_descends (prefixWord ++ tailWord_817004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817022 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_817022 : Nat := 118140960795 + 817022 * 2 ^ 59
def prefixEnd_817022 : Nat := 4983230072969 + 3 ^ 40 * 817022 * 2
def baseEnd_817022 : Nat := 419524991297807631367591

theorem tailTrace_817022 : CollatzResearch.WordTrace tailWord_817022 prefixEnd_817022 419524991297807631367591 := by
  unfold tailWord_817022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724905055759538136707665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19866160297384203395774213 3724905055759538136707665)
  ·
    refine ⟨2793678791819653602530749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3724905055759538136707665 2793678791819653602530749)
    ·
      refine ⟨1047629546932370100949031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2793678791819653602530749 1047629546932370100949031)
      ·
        refine ⟨1571444320398555151423547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047629546932370100949031 1571444320398555151423547)
        ·
          refine ⟨2357166480597832727135321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571444320398555151423547 2357166480597832727135321)
          ·
            refine ⟨1767874860448374545351491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357166480597832727135321 1767874860448374545351491)
            ·
              refine ⟨2651812290672561818027237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767874860448374545351491 2651812290672561818027237)
              ·
                refine ⟨497214804501105340880107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2651812290672561818027237 497214804501105340880107)
                ·
                  refine ⟨745822206751658011320161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497214804501105340880107 745822206751658011320161)
                  ·
                    refine ⟨559366655063743508490121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 745822206751658011320161 559366655063743508490121)
                    ·
                      refine ⟨419524991297807631367591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559366655063743508490121 419524991297807631367591)
                      ·
                        rfl

theorem cell23_817022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_817022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817022 prefixEnd_817022 := by exact prefixLift 817022
  have htrace : WordTrace (prefixWord ++ tailWord_817022) baseStart_817022 baseEnd_817022 := by
    simpa [prefixWord, tailWord_817022, baseEnd_817022] using wordTrace_append hprefix tailTrace_817022
  have hstable : (prefixWord ++ tailWord_817022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817022).length < 2 ^ (prefixWord ++ tailWord_817022).sum := by decide
  have hdescent : baseEnd_817022 < baseStart_817022 := by decide
  rcases family_descends (prefixWord ++ tailWord_817022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817027 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_817027 : Nat := 118140960795 + 817027 * 2 ^ 59
def prefixEnd_817027 : Nat := 4983230072969 + 3 ^ 40 * 817027 * 2
def baseEnd_817027 : Nat := 419527558701080111805067

theorem tailTrace_817027 : CollatzResearch.WordTrace tailWord_817027 prefixEnd_817027 419527558701080111805067 := by
  unfold tailWord_817027
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799422811058190947593335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19866281874038793965062223 29799422811058190947593335)
  ·
    refine ⟨44699134216587286421390003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29799422811058190947593335 44699134216587286421390003)
    ·
      refine ⟨67048701324880929632085005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44699134216587286421390003 67048701324880929632085005)
      ·
        refine ⟨25143262996830348612031877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67048701324880929632085005 25143262996830348612031877)
        ·
          refine ⟨4714361811905690364755977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25143262996830348612031877 4714361811905690364755977)
          ·
            refine ⟨3535771358929267773566983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714361811905690364755977 3535771358929267773566983)
            ·
              refine ⟨5303657038393901660350475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535771358929267773566983 5303657038393901660350475)
              ·
                refine ⟨7955485557590852490525713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303657038393901660350475 7955485557590852490525713)
                ·
                  refine ⟨5966614168193139367894285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955485557590852490525713 5966614168193139367894285)
                  ·
                    refine ⟨2237480313072427262960357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5966614168193139367894285 2237480313072427262960357)
                    ·
                      refine ⟨419527558701080111805067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2237480313072427262960357 419527558701080111805067)
                      ·
                        rfl

theorem cell23_817027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_817027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817027 prefixEnd_817027 := by exact prefixLift 817027
  have htrace : WordTrace (prefixWord ++ tailWord_817027) baseStart_817027 baseEnd_817027 := by
    simpa [prefixWord, tailWord_817027, baseEnd_817027] using wordTrace_append hprefix tailTrace_817027
  have hstable : (prefixWord ++ tailWord_817027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817027).length < 2 ^ (prefixWord ++ tailWord_817027).sum := by decide
  have hdescent : baseEnd_817027 < baseStart_817027 := by decide
  rcases family_descends (prefixWord ++ tailWord_817027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817038 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_817038 : Nat := 118140960795 + 817038 * 2 ^ 59
def prefixEnd_817038 : Nat := 4983230072969 + 3 ^ 40 * 817038 * 2
def baseEnd_817038 : Nat := 419533206988279568767517

theorem tailTrace_817038 : CollatzResearch.WordTrace tailWord_817038 prefixEnd_817038 419533206988279568767517 := by
  unfold tailWord_817038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724978001752292478280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19866549342678893217495845 3724978001752292478280471)
  ·
    refine ⟨5587467002628438717420707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724978001752292478280471 5587467002628438717420707)
    ·
      refine ⟨8381200503942658076131061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587467002628438717420707 8381200503942658076131061)
      ·
        refine ⟨785737547244624194637287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8381200503942658076131061 785737547244624194637287)
        ·
          refine ⟨1178606320866936291955931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785737547244624194637287 1178606320866936291955931)
          ·
            refine ⟨1767909481300404437933897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178606320866936291955931 1767909481300404437933897)
            ·
              refine ⟨1325932110975303328450423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767909481300404437933897 1325932110975303328450423)
              ·
                refine ⟨1988898166462954992675635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325932110975303328450423 1988898166462954992675635)
                ·
                  refine ⟨2983347249694432489013453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988898166462954992675635 2983347249694432489013453)
                  ·
                    refine ⟨1118755218635412183380045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983347249694432489013453 1118755218635412183380045)
                    ·
                      refine ⟨419533206988279568767517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118755218635412183380045 419533206988279568767517)
                      ·
                        rfl

theorem cell23_817038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_817038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817038 prefixEnd_817038 := by exact prefixLift 817038
  have htrace : WordTrace (prefixWord ++ tailWord_817038) baseStart_817038 baseEnd_817038 := by
    simpa [prefixWord, tailWord_817038, baseEnd_817038] using wordTrace_append hprefix tailTrace_817038
  have hstable : (prefixWord ++ tailWord_817038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817038).length < 2 ^ (prefixWord ++ tailWord_817038).sum := by decide
  have hdescent : baseEnd_817038 < baseStart_817038 := by decide
  rcases family_descends (prefixWord ++ tailWord_817038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817097 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_817097 : Nat := 118140960795 + 817097 * 2 ^ 59
def prefixEnd_817097 : Nat := 4983230072969 + 3 ^ 40 * 817097 * 2
def baseEnd_817097 : Nat := 139854500782298279309915

theorem tailTrace_817097 : CollatzResearch.WordTrace tailWord_817097 prefixEnd_817097 139854500782298279309915 := by
  unfold tailWord_817097
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801975920804592902641545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19867983947203061935094363 29801975920804592902641545)
  ·
    refine ⟨22351481940603444676981159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29801975920804592902641545 22351481940603444676981159)
    ·
      refine ⟨33527222910905167015471739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351481940603444676981159 33527222910905167015471739)
      ·
        refine ⟨50290834366357750523207609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33527222910905167015471739 50290834366357750523207609)
        ·
          refine ⟨37718125774768312892405707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50290834366357750523207609 37718125774768312892405707)
          ·
            refine ⟨56577188662152469338608561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37718125774768312892405707 56577188662152469338608561)
            ·
              refine ⟨42432891496614352003956421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56577188662152469338608561 42432891496614352003956421)
              ·
                refine ⟨7956167155615191000741829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42432891496614352003956421 7956167155615191000741829)
                ·
                  refine ⟨1491781341677848312639093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7956167155615191000741829 1491781341677848312639093)
                  ·
                    refine ⟨139854500782298279309915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1491781341677848312639093 139854500782298279309915)
                    ·
                      rfl

theorem cell23_817097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_817097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817097 prefixEnd_817097 := by exact prefixLift 817097
  have htrace : WordTrace (prefixWord ++ tailWord_817097) baseStart_817097 baseEnd_817097 := by
    simpa [prefixWord, tailWord_817097, baseEnd_817097] using wordTrace_append hprefix tailTrace_817097
  have hstable : (prefixWord ++ tailWord_817097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817097).length < 2 ^ (prefixWord ++ tailWord_817097).sum := by decide
  have hdescent : baseEnd_817097 < baseStart_817097 := by decide
  rcases family_descends (prefixWord ++ tailWord_817097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817104 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2]
def baseStart_817104 : Nat := 118140960795 + 817104 * 2 ^ 59
def prefixEnd_817104 : Nat := 4983230072969 + 3 ^ 40 * 817104 * 2
def baseEnd_817104 : Nat := 419567096711476310542213

theorem tailTrace_817104 : CollatzResearch.WordTrace tailWord_817104 prefixEnd_817104 419567096711476310542213 := by
  unfold tailWord_817104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901115615889616549073183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19868154154519488732097577 14901115615889616549073183)
  ·
    refine ⟨22351673423834424823609775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14901115615889616549073183 22351673423834424823609775)
    ·
      refine ⟨33527510135751637235414663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351673423834424823609775 33527510135751637235414663)
      ·
        refine ⟨50291265203627455853121995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33527510135751637235414663 50291265203627455853121995)
        ·
          refine ⟨75436897805441183779682993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50291265203627455853121995 75436897805441183779682993)
          ·
            refine ⟨56577673354080887834762245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75436897805441183779682993 56577673354080887834762245)
            ·
              refine ⟨10608313753890166469017921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56577673354080887834762245 10608313753890166469017921)
              ·
                refine ⟨7956235315417624851763441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10608313753890166469017921 7956235315417624851763441)
                ·
                  refine ⟨5967176486563218638822581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956235315417624851763441 5967176486563218638822581)
                  ·
                    refine ⟨559422795615301747389617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5967176486563218638822581 559422795615301747389617)
                    ·
                      refine ⟨419567096711476310542213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559422795615301747389617 419567096711476310542213)
                      ·
                        rfl

theorem cell23_817104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2].length) (baseStart_817104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817104 prefixEnd_817104 := by exact prefixLift 817104
  have htrace : WordTrace (prefixWord ++ tailWord_817104) baseStart_817104 baseEnd_817104 := by
    simpa [prefixWord, tailWord_817104, baseEnd_817104] using wordTrace_append hprefix tailTrace_817104
  have hstable : (prefixWord ++ tailWord_817104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817104).length < 2 ^ (prefixWord ++ tailWord_817104).sum := by decide
  have hdescent : baseEnd_817104 < baseStart_817104 := by decide
  rcases family_descends (prefixWord ++ tailWord_817104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817147 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_817147 : Nat := 118140960795 + 817147 * 2 ^ 59
def prefixEnd_817147 : Nat := 4983230072969 + 3 ^ 40 * 817147 * 2
def baseEnd_817147 : Nat := 419589176379619642304515

theorem tailTrace_817147 : CollatzResearch.WordTrace tailWord_817147 prefixEnd_817147 419589176379619642304515 := by
  unfold tailWord_817147
  simp only [CollatzResearch.WordTrace]
  refine ⟨29803799570623451441961695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19869199713748967627974463 29803799570623451441961695)
  ·
    refine ⟨44705699355935177162942543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29803799570623451441961695 44705699355935177162942543)
    ·
      refine ⟨67058549033902765744413815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44705699355935177162942543 67058549033902765744413815)
      ·
        refine ⟨100587823550854148616620723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67058549033902765744413815 100587823550854148616620723)
        ·
          refine ⟨150881735326281222924931085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100587823550854148616620723 150881735326281222924931085)
          ·
            refine ⟨56580650747355458596849157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150881735326281222924931085 56580650747355458596849157)
            ·
              refine ⟨10608872015129148486909217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56580650747355458596849157 10608872015129148486909217)
              ·
                refine ⟨7956654011346861365181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10608872015129148486909217 7956654011346861365181913)
                ·
                  refine ⟨5967490508510146023886435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956654011346861365181913 5967490508510146023886435)
                  ·
                    refine ⟨8951235762765219035829653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967490508510146023886435 8951235762765219035829653)
                    ·
                      refine ⟨419589176379619642304515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8951235762765219035829653 419589176379619642304515)
                      ·
                        rfl

theorem cell23_817147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_817147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817147 prefixEnd_817147 := by exact prefixLift 817147
  have htrace : WordTrace (prefixWord ++ tailWord_817147) baseStart_817147 baseEnd_817147 := by
    simpa [prefixWord, tailWord_817147, baseEnd_817147] using wordTrace_append hprefix tailTrace_817147
  have hstable : (prefixWord ++ tailWord_817147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817147).length < 2 ^ (prefixWord ++ tailWord_817147).sum := by decide
  have hdescent : baseEnd_817147 < baseStart_817147 := by decide
  rcases family_descends (prefixWord ++ tailWord_817147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817177 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_817177 : Nat := 118140960795 + 817177 * 2 ^ 59
def prefixEnd_817177 : Nat := 4983230072969 + 3 ^ 40 * 817177 * 2
def baseEnd_817177 : Nat := 419604580799254524929377

theorem tailTrace_817177 : CollatzResearch.WordTrace tailWord_817177 prefixEnd_817177 419604580799254524929377 := by
  unfold tailWord_817177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29804893760514766565553785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19869929173676511043702523 29804893760514766565553785)
  ·
    refine ⟨22353670320386074924165339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29804893760514766565553785 22353670320386074924165339)
    ·
      refine ⟨33530505480579112386248009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22353670320386074924165339 33530505480579112386248009)
      ·
        refine ⟨25147879110434334289686007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33530505480579112386248009 25147879110434334289686007)
        ·
          refine ⟨37721818665651501434529011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25147879110434334289686007 37721818665651501434529011)
          ·
            refine ⟨56582727998477252151793517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37721818665651501434529011 56582727998477252151793517)
            ·
              refine ⟨21218522999428969556922569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56582727998477252151793517 21218522999428969556922569)
              ·
                refine ⟨15913892249571727167691927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21218522999428969556922569 15913892249571727167691927)
                ·
                  refine ⟨23870838374357590751537891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913892249571727167691927 23870838374357590751537891)
                  ·
                    refine ⟨35806257561536386127306837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23870838374357590751537891 35806257561536386127306837)
                    ·
                      refine ⟨419604580799254524929377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 35806257561536386127306837 419604580799254524929377)
                      ·
                        rfl

theorem cell23_817177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_817177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817177 prefixEnd_817177 := by exact prefixLift 817177
  have htrace : WordTrace (prefixWord ++ tailWord_817177) baseStart_817177 baseEnd_817177 := by
    simpa [prefixWord, tailWord_817177, baseEnd_817177] using wordTrace_append hprefix tailTrace_817177
  have hstable : (prefixWord ++ tailWord_817177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817177).length < 2 ^ (prefixWord ++ tailWord_817177).sum := by decide
  have hdescent : baseEnd_817177 < baseStart_817177 := by decide
  rcases family_descends (prefixWord ++ tailWord_817177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817228 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_817228 : Nat := 118140960795 + 817228 * 2 ^ 59
def prefixEnd_817228 : Nat := 4983230072969 + 3 ^ 40 * 817228 * 2
def baseEnd_817228 : Nat := 419630768312633825391643

theorem tailTrace_817228 : CollatzResearch.WordTrace tailWord_817228 prefixEnd_817228 419630768312633825391643 := by
  unfold tailWord_817228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903376941665001137830169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19871169255553334850440225 14903376941665001137830169)
  ·
    refine ⟨11177532706248750853372627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14903376941665001137830169 11177532706248750853372627)
    ·
      refine ⟨16766299059373126280058941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11177532706248750853372627 16766299059373126280058941)
      ·
        refine ⟨6287362147264922355022103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16766299059373126280058941 6287362147264922355022103)
        ·
          refine ⟨9431043220897383532533155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287362147264922355022103 9431043220897383532533155)
          ·
            refine ⟨14146564831346075298799733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431043220897383532533155 14146564831346075298799733)
            ·
              refine ⟨1326240452938694559262475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14146564831346075298799733 1326240452938694559262475)
              ·
                refine ⟨1989360679408041838893713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326240452938694559262475 1989360679408041838893713)
                ·
                  refine ⟨1492020509556031379170285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989360679408041838893713 1492020509556031379170285)
                  ·
                    refine ⟨559507691083511767188857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492020509556031379170285 559507691083511767188857)
                    ·
                      refine ⟨419630768312633825391643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559507691083511767188857 419630768312633825391643)
                      ·
                        rfl

theorem cell23_817228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_817228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817228 prefixEnd_817228 := by exact prefixLift 817228
  have htrace : WordTrace (prefixWord ++ tailWord_817228) baseStart_817228 baseEnd_817228 := by
    simpa [prefixWord, tailWord_817228, baseEnd_817228] using wordTrace_append hprefix tailTrace_817228
  have hstable : (prefixWord ++ tailWord_817228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817228).length < 2 ^ (prefixWord ++ tailWord_817228).sum := by decide
  have hdescent : baseEnd_817228 < baseStart_817228 := by decide
  rcases family_descends (prefixWord ++ tailWord_817228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817241 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_817241 : Nat := 118140960795 + 817241 * 2 ^ 59
def prefixEnd_817241 : Nat := 4983230072969 + 3 ^ 40 * 817241 * 2
def baseEnd_817241 : Nat := 419637443561142274529083

theorem tailTrace_817241 : CollatzResearch.WordTrace tailWord_817241 prefixEnd_817241 419637443561142274529083 := by
  unfold tailWord_817241
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807228032282905495883577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19871485354855270330589051 29807228032282905495883577)
  ·
    refine ⟨22355421024212179121912683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29807228032282905495883577 22355421024212179121912683)
    ·
      refine ⟨33533131536318268682869025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355421024212179121912683 33533131536318268682869025)
      ·
        refine ⟨25149848652238701512151769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33533131536318268682869025 25149848652238701512151769)
        ·
          refine ⟨18862386489179026134113827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25149848652238701512151769 18862386489179026134113827)
          ·
            refine ⟨28293579733768539201170741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18862386489179026134113827 28293579733768539201170741)
            ·
              refine ⟨2652523100040800550109757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28293579733768539201170741 2652523100040800550109757)
              ·
                refine ⟨994696162515300206291159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652523100040800550109757 994696162515300206291159)
                ·
                  refine ⟨1492044243772950309436739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994696162515300206291159 1492044243772950309436739)
                  ·
                    refine ⟨2238066365659425464155109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1492044243772950309436739 2238066365659425464155109)
                    ·
                      refine ⟨419637443561142274529083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2238066365659425464155109 419637443561142274529083)
                      ·
                        rfl

theorem cell23_817241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_817241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817241 prefixEnd_817241 := by exact prefixLift 817241
  have htrace : WordTrace (prefixWord ++ tailWord_817241) baseStart_817241 baseEnd_817241 := by
    simpa [prefixWord, tailWord_817241, baseEnd_817241] using wordTrace_append hprefix tailTrace_817241
  have hstable : (prefixWord ++ tailWord_817241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817241).length < 2 ^ (prefixWord ++ tailWord_817241).sum := by decide
  have hdescent : baseEnd_817241 < baseStart_817241 := by decide
  rcases family_descends (prefixWord ++ tailWord_817241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817261 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_817261 : Nat := 118140960795 + 817261 * 2 ^ 59
def prefixEnd_817261 : Nat := 4983230072969 + 3 ^ 40 * 817261 * 2
def baseEnd_817261 : Nat := 419647713174232196278991

theorem tailTrace_817261 : CollatzResearch.WordTrace tailWord_817261 prefixEnd_817261 419647713174232196278991 := by
  unfold tailWord_817261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807957492210448911611637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19871971661473632607741091 29807957492210448911611637)
  ·
    refine ⟨2794496014894729585463591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29807957492210448911611637 2794496014894729585463591)
    ·
      refine ⟨4191744022342094378195387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794496014894729585463591 4191744022342094378195387)
      ·
        refine ⟨6287616033513141567293081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191744022342094378195387 6287616033513141567293081)
        ·
          refine ⟨4715712025134856175469811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6287616033513141567293081 4715712025134856175469811)
          ·
            refine ⟨7073568037702284263204717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715712025134856175469811 7073568037702284263204717)
            ·
              refine ⟨2652588014138356598701769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7073568037702284263204717 2652588014138356598701769)
              ·
                refine ⟨1989441010603767449026327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652588014138356598701769 1989441010603767449026327)
                ·
                  refine ⟨2984161515905651173539491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989441010603767449026327 2984161515905651173539491)
                  ·
                    refine ⟨4476242273858476760309237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2984161515905651173539491 4476242273858476760309237)
                    ·
                      refine ⟨419647713174232196278991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4476242273858476760309237 419647713174232196278991)
                      ·
                        rfl

theorem cell23_817261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_817261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817261 prefixEnd_817261 := by exact prefixLift 817261
  have htrace : WordTrace (prefixWord ++ tailWord_817261) baseStart_817261 baseEnd_817261 := by
    simpa [prefixWord, tailWord_817261, baseEnd_817261] using wordTrace_append hprefix tailTrace_817261
  have hstable : (prefixWord ++ tailWord_817261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817261).length < 2 ^ (prefixWord ++ tailWord_817261).sum := by decide
  have hdescent : baseEnd_817261 < baseStart_817261 := by decide
  rcases family_descends (prefixWord ++ tailWord_817261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817271 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_817271 : Nat := 118140960795 + 817271 * 2 ^ 59
def prefixEnd_817271 : Nat := 4983230072969 + 3 ^ 40 * 817271 * 2
def baseEnd_817271 : Nat := 419652847980777157153945

theorem tailTrace_817271 : CollatzResearch.WordTrace tailWord_817271 prefixEnd_817271 419652847980777157153945 := by
  unfold tailWord_817271
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808322222174220619475667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19872214814782813746317111 29808322222174220619475667)
  ·
    refine ⟨44712483333261330929213501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29808322222174220619475667 44712483333261330929213501)
    ·
      refine ⟨16767181249972999098455063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44712483333261330929213501 16767181249972999098455063)
      ·
        refine ⟨25150771874959498647682595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16767181249972999098455063 25150771874959498647682595)
        ·
          refine ⟨37726157812439247971523893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25150771874959498647682595 37726157812439247971523893)
          ·
            refine ⟨3536827294916179497330365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37726157812439247971523893 3536827294916179497330365)
            ·
              refine ⟨1326310235593567311498887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3536827294916179497330365 1326310235593567311498887)
              ·
                refine ⟨1989465353390350967248331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326310235593567311498887 1989465353390350967248331)
                ·
                  refine ⟨2984198030085526450872497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989465353390350967248331 2984198030085526450872497)
                  ·
                    refine ⟨2238148522564144838154373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984198030085526450872497 2238148522564144838154373)
                    ·
                      refine ⟨419652847980777157153945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2238148522564144838154373 419652847980777157153945)
                      ·
                        rfl

theorem cell23_817271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_817271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817271 prefixEnd_817271 := by exact prefixLift 817271
  have htrace : WordTrace (prefixWord ++ tailWord_817271) baseStart_817271 baseEnd_817271 := by
    simpa [prefixWord, tailWord_817271, baseEnd_817271] using wordTrace_append hprefix tailTrace_817271
  have hstable : (prefixWord ++ tailWord_817271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817271).length < 2 ^ (prefixWord ++ tailWord_817271).sum := by decide
  have hdescent : baseEnd_817271 < baseStart_817271 := by decide
  rcases family_descends (prefixWord ++ tailWord_817271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817281 : List Nat := [1, 2, 4, 2, 3, 1, 1, 9]
def baseStart_817281 : Nat := 118140960795 + 817281 * 2 ^ 59
def prefixEnd_817281 : Nat := 4983230072969 + 3 ^ 40 * 817281 * 2
def baseEnd_817281 : Nat := 15542888251382300667737

theorem tailTrace_817281 : CollatzResearch.WordTrace tailWord_817281 prefixEnd_817281 15542888251382300667737 := by
  unfold tailWord_817281
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808686952137992327339697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19872457968091994884893131 29808686952137992327339697)
  ·
    refine ⟨22356515214103494245504773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29808686952137992327339697 22356515214103494245504773)
    ·
      refine ⟨4191846602644405171032145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22356515214103494245504773 4191846602644405171032145)
      ·
        refine ⟨3143884951983303878274109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191846602644405171032145 3143884951983303878274109)
        ·
          refine ⟨1178956856993738954352791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3143884951983303878274109 1178956856993738954352791)
          ·
            refine ⟨1768435285490608431529187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178956856993738954352791 1768435285490608431529187)
            ·
              refine ⟨2652652928235912647293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768435285490608431529187 2652652928235912647293781)
              ·
                refine ⟨15542888251382300667737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2652652928235912647293781 15542888251382300667737)
                ·
                  rfl

theorem cell23_817281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 9].length) (baseStart_817281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817281 prefixEnd_817281 := by exact prefixLift 817281
  have htrace : WordTrace (prefixWord ++ tailWord_817281) baseStart_817281 baseEnd_817281 := by
    simpa [prefixWord, tailWord_817281, baseEnd_817281] using wordTrace_append hprefix tailTrace_817281
  have hstable : (prefixWord ++ tailWord_817281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817281).length < 2 ^ (prefixWord ++ tailWord_817281).sum := by decide
  have hdescent : baseEnd_817281 < baseStart_817281 := by decide
  rcases family_descends (prefixWord ++ tailWord_817281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817308 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_817308 : Nat := 118140960795 + 817308 * 2 ^ 59
def prefixEnd_817308 : Nat := 4983230072969 + 3 ^ 40 * 817308 * 2
def baseEnd_817308 : Nat := 419671846764993512391275

theorem tailTrace_817308 : CollatzResearch.WordTrace tailWord_817308 prefixEnd_817308 419671846764993512391275 := by
  unfold tailWord_817308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904835861520087969286289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19873114482026783959048385 14904835861520087969286289)
  ·
    refine ⟨11178626896140065976964717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14904835861520087969286289 11178626896140065976964717)
    ·
      refine ⟨4191985086052524741361769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11178626896140065976964717 4191985086052524741361769)
      ·
        refine ⟨3143988814539393556021327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191985086052524741361769 3143988814539393556021327)
        ·
          refine ⟨4715983221809090334031991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143988814539393556021327 4715983221809090334031991)
          ·
            refine ⟨7073974832713635501047987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715983221809090334031991 7073974832713635501047987)
            ·
              refine ⟨10610962249070453251571981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073974832713635501047987 10610962249070453251571981)
              ·
                refine ⟨3979110843401419969339493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10610962249070453251571981 3979110843401419969339493)
                ·
                  refine ⟨746083283137766244251155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3979110843401419969339493 746083283137766244251155)
                  ·
                    refine ⟨1119124924706649366376733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746083283137766244251155 1119124924706649366376733)
                    ·
                      refine ⟨419671846764993512391275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1119124924706649366376733 419671846764993512391275)
                      ·
                        rfl

theorem cell23_817308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_817308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817308 prefixEnd_817308 := by exact prefixLift 817308
  have htrace : WordTrace (prefixWord ++ tailWord_817308) baseStart_817308 baseEnd_817308 := by
    simpa [prefixWord, tailWord_817308, baseEnd_817308] using wordTrace_append hprefix tailTrace_817308
  have hstable : (prefixWord ++ tailWord_817308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817308).length < 2 ^ (prefixWord ++ tailWord_817308).sum := by decide
  have hdescent : baseEnd_817308 < baseStart_817308 := by decide
  rcases family_descends (prefixWord ++ tailWord_817308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817309 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_817309 : Nat := 118140960795 + 817309 * 2 ^ 59
def prefixEnd_817309 : Nat := 4983230072969 + 3 ^ 40 * 817309 * 2
def baseEnd_817309 : Nat := 419672360245648008478771

theorem tailTrace_817309 : CollatzResearch.WordTrace tailWord_817309 prefixEnd_817309 419672360245648008478771 := by
  unfold tailWord_817309
  simp only [CollatzResearch.WordTrace]
  refine ⟨29809708196036553109358981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19873138797357702072905987 29809708196036553109358981)
  ·
    refine ⟨5589320286756853708004809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29809708196036553109358981 5589320286756853708004809)
    ·
      refine ⟨4191990215067640281003607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589320286756853708004809 4191990215067640281003607)
      ·
        refine ⟨6287985322601460421505411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191990215067640281003607 6287985322601460421505411)
        ·
          refine ⟨9431977983902190632258117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287985322601460421505411 9431977983902190632258117)
          ·
            refine ⟨1768495871981660743548397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9431977983902190632258117 1768495871981660743548397)
            ·
              refine ⟨663185951993122778830649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1768495871981660743548397 663185951993122778830649)
              ·
                refine ⟨497389463994842084122987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663185951993122778830649 497389463994842084122987)
                ·
                  refine ⟨746084195992263126184481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497389463994842084122987 746084195992263126184481)
                  ·
                    refine ⟨559563146994197344638361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746084195992263126184481 559563146994197344638361)
                    ·
                      refine ⟨419672360245648008478771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559563146994197344638361 419672360245648008478771)
                      ·
                        rfl

theorem cell23_817309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_817309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817309 prefixEnd_817309 := by exact prefixLift 817309
  have htrace : WordTrace (prefixWord ++ tailWord_817309) baseStart_817309 baseEnd_817309 := by
    simpa [prefixWord, tailWord_817309, baseEnd_817309] using wordTrace_append hprefix tailTrace_817309
  have hstable : (prefixWord ++ tailWord_817309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817309).length < 2 ^ (prefixWord ++ tailWord_817309).sum := by decide
  have hdescent : baseEnd_817309 < baseStart_817309 := by decide
  rcases family_descends (prefixWord ++ tailWord_817309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817319 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 2, 4]
def baseStart_817319 : Nat := 118140960795 + 817319 * 2 ^ 59
def prefixEnd_817319 : Nat := 4983230072969 + 3 ^ 40 * 817319 * 2
def baseEnd_817319 : Nat := 139892498350730989784575

theorem tailTrace_817319 : CollatzResearch.WordTrace tailWord_817319 prefixEnd_817319 139892498350730989784575 := by
  unfold tailWord_817319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29810072926000324817223011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19873381950666883211482007 29810072926000324817223011)
  ·
    refine ⟨44715109389000487225834517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29810072926000324817223011 44715109389000487225834517)
    ·
      refine ⟨2096020752609397838710993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44715109389000487225834517 2096020752609397838710993)
      ·
        refine ⟨1572015564457048379033245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2096020752609397838710993 1572015564457048379033245)
        ·
          refine ⟨589505836671393142137467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1572015564457048379033245 589505836671393142137467)
          ·
            refine ⟨884258755007089713206201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589505836671393142137467 884258755007089713206201)
            ·
              refine ⟨663194066255317284904651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884258755007089713206201 663194066255317284904651)
              ·
                refine ⟨994791099382975927356977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663194066255317284904651 994791099382975927356977)
                ·
                  refine ⟨746093324537231945517733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994791099382975927356977 746093324537231945517733)
                  ·
                    refine ⟨139892498350730989784575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746093324537231945517733 139892498350730989784575)
                    ·
                      rfl

theorem cell23_817319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_817319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817319 prefixEnd_817319 := by exact prefixLift 817319
  have htrace : WordTrace (prefixWord ++ tailWord_817319) baseStart_817319 baseEnd_817319 := by
    simpa [prefixWord, tailWord_817319, baseEnd_817319] using wordTrace_append hprefix tailTrace_817319
  have hstable : (prefixWord ++ tailWord_817319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817319).length < 2 ^ (prefixWord ++ tailWord_817319).sum := by decide
  have hdescent : baseEnd_817319 < baseStart_817319 := by decide
  rcases family_descends (prefixWord ++ tailWord_817319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817324 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_817324 : Nat := 118140960795 + 817324 * 2 ^ 59
def prefixEnd_817324 : Nat := 4983230072969 + 3 ^ 40 * 817324 * 2
def baseEnd_817324 : Nat := 139893354151821816597067

theorem tailTrace_817324 : CollatzResearch.WordTrace tailWord_817324 prefixEnd_817324 139893354151821816597067 := by
  unfold tailWord_817324
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905127645491105335577513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19873503527321473780770017 14905127645491105335577513)
  ·
    refine ⟨11178845734118329001683135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14905127645491105335577513 11178845734118329001683135)
    ·
      refine ⟨16768268601177493502524703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178845734118329001683135 16768268601177493502524703)
      ·
        refine ⟨25152402901766240253787055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768268601177493502524703 25152402901766240253787055)
        ·
          refine ⟨37728604352649360380680583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25152402901766240253787055 37728604352649360380680583)
          ·
            refine ⟨56592906528974040571020875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37728604352649360380680583 56592906528974040571020875)
            ·
              refine ⟨84889359793461060856531313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56592906528974040571020875 84889359793461060856531313)
              ·
                refine ⟨63667019845095795642398485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84889359793461060856531313 63667019845095795642398485)
                ·
                  refine ⟨2984391555238865420737429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63667019845095795642398485 2984391555238865420737429)
                  ·
                    refine ⟨139893354151821816597067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2984391555238865420737429 139893354151821816597067)
                    ·
                      rfl

theorem cell23_817324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_817324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817324 prefixEnd_817324 := by exact prefixLift 817324
  have htrace : WordTrace (prefixWord ++ tailWord_817324) baseStart_817324 baseEnd_817324 := by
    simpa [prefixWord, tailWord_817324, baseEnd_817324] using wordTrace_append hprefix tailTrace_817324
  have hstable : (prefixWord ++ tailWord_817324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817324).length < 2 ^ (prefixWord ++ tailWord_817324).sum := by decide
  have hdescent : baseEnd_817324 < baseStart_817324 := by decide
  rcases family_descends (prefixWord ++ tailWord_817324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817335 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_817335 : Nat := 118140960795 + 817335 * 2 ^ 59
def prefixEnd_817335 : Nat := 4983230072969 + 3 ^ 40 * 817335 * 2
def baseEnd_817335 : Nat := 419685710742664906753651

theorem tailTrace_817335 : CollatzResearch.WordTrace tailWord_817335 prefixEnd_817335 419685710742664906753651 := by
  unfold tailWord_817335
  simp only [CollatzResearch.WordTrace]
  refine ⟨29810656493942359549805459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19873770995961573033203639 29810656493942359549805459)
  ·
    refine ⟨44715984740913539324708189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29810656493942359549805459 44715984740913539324708189)
    ·
      refine ⟨16768494277842577246765571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44715984740913539324708189 16768494277842577246765571)
      ·
        refine ⟨25152741416763865870148357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768494277842577246765571 25152741416763865870148357)
        ·
          refine ⟨4716139015643224850652817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25152741416763865870148357 4716139015643224850652817)
          ·
            refine ⟨3537104261732418637989613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716139015643224850652817 3537104261732418637989613)
            ·
              refine ⟨1326414098149656989246105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537104261732418637989613 1326414098149656989246105)
              ·
                refine ⟨994810573612242741934579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326414098149656989246105 994810573612242741934579)
                ·
                  refine ⟨1492215860418364112901869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994810573612242741934579 1492215860418364112901869)
                  ·
                    refine ⟨559580947656886542338201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492215860418364112901869 559580947656886542338201)
                    ·
                      refine ⟨419685710742664906753651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559580947656886542338201 419685710742664906753651)
                      ·
                        rfl

theorem cell23_817335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_817335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817335 prefixEnd_817335 := by exact prefixLift 817335
  have htrace : WordTrace (prefixWord ++ tailWord_817335) baseStart_817335 baseEnd_817335 := by
    simpa [prefixWord, tailWord_817335, baseEnd_817335] using wordTrace_append hprefix tailTrace_817335
  have hstable : (prefixWord ++ tailWord_817335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817335).length < 2 ^ (prefixWord ++ tailWord_817335).sum := by decide
  have hdescent : baseEnd_817335 < baseStart_817335 := by decide
  rcases family_descends (prefixWord ++ tailWord_817335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817401 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_817401 : Nat := 118140960795 + 817401 * 2 ^ 59
def prefixEnd_817401 : Nat := 4983230072969 + 3 ^ 40 * 817401 * 2
def baseEnd_817401 : Nat := 139906533488620549509449

theorem tailTrace_817401 : CollatzResearch.WordTrace tailWord_817401 prefixEnd_817401 139906533488620549509449 := by
  unfold tailWord_817401
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813063711703252821708057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19875375807802168547805371 29813063711703252821708057)
  ·
    refine ⟨22359797783777439616281043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29813063711703252821708057 22359797783777439616281043)
    ·
      refine ⟨33539696675666159424421565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22359797783777439616281043 33539696675666159424421565)
      ·
        refine ⟨12577386253374809784158087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33539696675666159424421565 12577386253374809784158087)
        ·
          refine ⟨18866079380062214676237131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12577386253374809784158087 18866079380062214676237131)
          ·
            refine ⟨28299119070093322014355697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18866079380062214676237131 28299119070093322014355697)
            ·
              refine ⟨21224339302569991510766773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28299119070093322014355697 21224339302569991510766773)
              ·
                refine ⟨1989781809615936704134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21224339302569991510766773 1989781809615936704134385)
                ·
                  refine ⟨1492336357211952528100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989781809615936704134385 1492336357211952528100789)
                  ·
                    refine ⟨139906533488620549509449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1492336357211952528100789 139906533488620549509449)
                    ·
                      rfl

theorem cell23_817401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_817401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817401 prefixEnd_817401 := by exact prefixLift 817401
  have htrace : WordTrace (prefixWord ++ tailWord_817401) baseStart_817401 baseEnd_817401 := by
    simpa [prefixWord, tailWord_817401, baseEnd_817401] using wordTrace_append hprefix tailTrace_817401
  have hstable : (prefixWord ++ tailWord_817401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817401).length < 2 ^ (prefixWord ++ tailWord_817401).sum := by decide
  have hdescent : baseEnd_817401 < baseStart_817401 := by decide
  rcases family_descends (prefixWord ++ tailWord_817401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817461 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 10]
def baseStart_817461 : Nat := 118140960795 + 817461 * 2 ^ 59
def prefixEnd_817461 : Nat := 4983230072969 + 3 ^ 40 * 817461 * 2
def baseEnd_817461 : Nat := 46638934367236823753119

theorem tailTrace_817461 : CollatzResearch.WordTrace tailWord_817461 prefixEnd_817461 46638934367236823753119 := by
  unfold tailWord_817461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815252091485883068892237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19876834727657255379261491 29815252091485883068892237)
  ·
    refine ⟨11180719534307206150834589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29815252091485883068892237 11180719534307206150834589)
    ·
      refine ⟨4192769825365202306562971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11180719534307206150834589 4192769825365202306562971)
      ·
        refine ⟨6289154738047803459844457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192769825365202306562971 6289154738047803459844457)
        ·
          refine ⟨4716866053535852594883343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6289154738047803459844457 4716866053535852594883343)
          ·
            refine ⟨7075299080303778892325015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716866053535852594883343 7075299080303778892325015)
            ·
              refine ⟨10612948620455668338487523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075299080303778892325015 10612948620455668338487523)
              ·
                refine ⟨15919422930683502507731285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612948620455668338487523 15919422930683502507731285)
                ·
                  refine ⟨46638934367236823753119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15919422930683502507731285 46638934367236823753119)
                  ·
                    rfl

theorem cell23_817461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_817461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817461 prefixEnd_817461 := by exact prefixLift 817461
  have htrace : WordTrace (prefixWord ++ tailWord_817461) baseStart_817461 baseEnd_817461 := by
    simpa [prefixWord, tailWord_817461, baseEnd_817461] using wordTrace_append hprefix tailTrace_817461
  have hstable : (prefixWord ++ tailWord_817461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817461).length < 2 ^ (prefixWord ++ tailWord_817461).sum := by decide
  have hdescent : baseEnd_817461 < baseStart_817461 := by decide
  rcases family_descends (prefixWord ++ tailWord_817461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817508 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_817508 : Nat := 118140960795 + 817508 * 2 ^ 59
def prefixEnd_817508 : Nat := 4983230072969 + 3 ^ 40 * 817508 * 2
def baseEnd_817508 : Nat := 139924847631964243296785

theorem tailTrace_817508 : CollatzResearch.WordTrace tailWord_817508 prefixEnd_817508 139924847631964243296785 := by
  unfold tailWord_817508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908483161157805047926589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19877977548210406730568785 14908483161157805047926589)
  ·
    refine ⟨5590681185434176892972471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14908483161157805047926589 5590681185434176892972471)
    ·
      refine ⟨8386021778151265339458707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590681185434176892972471 8386021778151265339458707)
      ·
        refine ⟨12579032667226898009188061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386021778151265339458707 12579032667226898009188061)
        ·
          refine ⟨4717137250210086753445523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12579032667226898009188061 4717137250210086753445523)
          ·
            refine ⟨7075705875315130130168285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717137250210086753445523 7075705875315130130168285)
            ·
              refine ⟨2653389703243173798813107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7075705875315130130168285 2653389703243173798813107)
              ·
                refine ⟨3980084554864760698219661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653389703243173798813107 3980084554864760698219661)
                ·
                  refine ⟨1492531708074285261832373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3980084554864760698219661 1492531708074285261832373)
                  ·
                    refine ⟨139924847631964243296785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1492531708074285261832373 139924847631964243296785)
                    ·
                      rfl

theorem cell23_817508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_817508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817508 prefixEnd_817508 := by exact prefixLift 817508
  have htrace : WordTrace (prefixWord ++ tailWord_817508) baseStart_817508 baseEnd_817508 := by
    simpa [prefixWord, tailWord_817508, baseEnd_817508] using wordTrace_append hprefix tailTrace_817508
  have hstable : (prefixWord ++ tailWord_817508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817508).length < 2 ^ (prefixWord ++ tailWord_817508).sum := by decide
  have hdescent : baseEnd_817508 < baseStart_817508 := by decide
  rcases family_descends (prefixWord ++ tailWord_817508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817539 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 1, 1, 3]
def baseStart_817539 : Nat := 118140960795 + 817539 * 2 ^ 59
def prefixEnd_817539 : Nat := 4983230072969 + 3 ^ 40 * 817539 * 2
def baseEnd_817539 : Nat := 419790460796182108602713

theorem tailTrace_817539 : CollatzResearch.WordTrace tailWord_817539 prefixEnd_817539 419790460796182108602713 := by
  unfold tailWord_817539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29818096985203302390231671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19878731323468868260154447 29818096985203302390231671)
  ·
    refine ⟨44727145477804953585347507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29818096985203302390231671 44727145477804953585347507)
    ·
      refine ⟨67090718216707430378021261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44727145477804953585347507 67090718216707430378021261)
      ·
        refine ⟨25159019331265286391757973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67090718216707430378021261 25159019331265286391757973)
        ·
          refine ⟨1179329031153060299613655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25159019331265286391757973 1179329031153060299613655)
          ·
            refine ⟨1768993546729590449420483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179329031153060299613655 1768993546729590449420483)
            ·
              refine ⟨2653490320094385674130725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768993546729590449420483 2653490320094385674130725)
              ·
                refine ⟨497529435017697313899511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2653490320094385674130725 497529435017697313899511)
                ·
                  refine ⟨746294152526545970849267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497529435017697313899511 746294152526545970849267)
                  ·
                    refine ⟨1119441228789818956273901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746294152526545970849267 1119441228789818956273901)
                    ·
                      refine ⟨419790460796182108602713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1119441228789818956273901 419790460796182108602713)
                      ·
                        rfl

theorem cell23_817539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_817539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817539 prefixEnd_817539 := by exact prefixLift 817539
  have htrace : WordTrace (prefixWord ++ tailWord_817539) baseStart_817539 baseEnd_817539 := by
    simpa [prefixWord, tailWord_817539, baseEnd_817539] using wordTrace_append hprefix tailTrace_817539
  have hstable : (prefixWord ++ tailWord_817539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817539).length < 2 ^ (prefixWord ++ tailWord_817539).sum := by decide
  have hdescent : baseEnd_817539 < baseStart_817539 := by decide
  rcases family_descends (prefixWord ++ tailWord_817539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817562 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_817562 : Nat := 118140960795 + 817562 * 2 ^ 59
def prefixEnd_817562 : Nat := 4983230072969 + 3 ^ 40 * 817562 * 2
def baseEnd_817562 : Nat := 419802270851235518615107

theorem tailTrace_817562 : CollatzResearch.WordTrace tailWord_817562 prefixEnd_817562 419802270851235518615107 := by
  unfold tailWord_817562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454733966029994329579735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19879290576079984878879293 7454733966029994329579735)
  ·
    refine ⟨11182100949044991494369603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7454733966029994329579735 11182100949044991494369603)
    ·
      refine ⟨16773151423567487241554405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11182100949044991494369603 16773151423567487241554405)
      ·
        refine ⟨3144965891918903857791451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16773151423567487241554405 3144965891918903857791451)
        ·
          refine ⟨4717448837878355786687177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144965891918903857791451 4717448837878355786687177)
          ·
            refine ⟨3538086628408766840015383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717448837878355786687177 3538086628408766840015383)
            ·
              refine ⟨5307129942613150260023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538086628408766840015383 5307129942613150260023075)
              ·
                refine ⟨7960694913919725390034613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307129942613150260023075 7960694913919725390034613)
                ·
                  refine ⟨746315148179974255315745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7960694913919725390034613 746315148179974255315745)
                  ·
                    refine ⟨559736361134980691486809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746315148179974255315745 559736361134980691486809)
                    ·
                      refine ⟨419802270851235518615107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559736361134980691486809 419802270851235518615107)
                      ·
                        rfl

theorem cell23_817562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_817562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817562 prefixEnd_817562 := by exact prefixLift 817562
  have htrace : WordTrace (prefixWord ++ tailWord_817562) baseStart_817562 baseEnd_817562 := by
    simpa [prefixWord, tailWord_817562, baseEnd_817562] using wordTrace_append hprefix tailTrace_817562
  have hstable : (prefixWord ++ tailWord_817562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817562).length < 2 ^ (prefixWord ++ tailWord_817562).sum := by decide
  have hdescent : baseEnd_817562 < baseStart_817562 := by decide
  rcases family_descends (prefixWord ++ tailWord_817562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817566 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_817566 : Nat := 118140960795 + 817566 * 2 ^ 59
def prefixEnd_817566 : Nat := 4983230072969 + 3 ^ 40 * 817566 * 2
def baseEnd_817566 : Nat := 419804324773853502965089

theorem tailTrace_817566 : CollatzResearch.WordTrace tailWord_817566 prefixEnd_817566 419804324773853502965089 := by
  unfold tailWord_817566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727385219513185750183069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19879387837403657334309701 3727385219513185750183069)
  ·
    refine ⟨1397769457317444656318651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3727385219513185750183069 1397769457317444656318651)
    ·
      refine ⟨2096654185976166984477977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397769457317444656318651 2096654185976166984477977)
      ·
        refine ⟨1572490639482125238358483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2096654185976166984477977 1572490639482125238358483)
        ·
          refine ⟨2358735959223187857537725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572490639482125238358483 2358735959223187857537725)
          ·
            refine ⟨884525984708695446576647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2358735959223187857537725 884525984708695446576647)
            ·
              refine ⟨1326788977063043169864971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884525984708695446576647 1326788977063043169864971)
              ·
                refine ⟨1990183465594564754797457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326788977063043169864971 1990183465594564754797457)
                ·
                  refine ⟨1492637599195923566098093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990183465594564754797457 1492637599195923566098093)
                  ·
                    refine ⟨559739099698471337286785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492637599195923566098093 559739099698471337286785)
                    ·
                      refine ⟨419804324773853502965089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559739099698471337286785 419804324773853502965089)
                      ·
                        rfl

theorem cell23_817566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_817566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817566 prefixEnd_817566 := by exact prefixLift 817566
  have htrace : WordTrace (prefixWord ++ tailWord_817566) baseStart_817566 baseEnd_817566 := by
    simpa [prefixWord, tailWord_817566, baseEnd_817566] using wordTrace_append hprefix tailTrace_817566
  have hstable : (prefixWord ++ tailWord_817566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817566).length < 2 ^ (prefixWord ++ tailWord_817566).sum := by decide
  have hdescent : baseEnd_817566 < baseStart_817566 := by decide
  rcases family_descends (prefixWord ++ tailWord_817566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817575 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_817575 : Nat := 118140960795 + 817575 * 2 ^ 59
def prefixEnd_817575 : Nat := 4983230072969 + 3 ^ 40 * 817575 * 2
def baseEnd_817575 : Nat := 419808946099743967752547

theorem tailTrace_817575 : CollatzResearch.WordTrace tailWord_817575 prefixEnd_817575 419808946099743967752547 := by
  unfold tailWord_817575
  simp only [CollatzResearch.WordTrace]
  refine ⟨29819410013072880538542179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19879606675381920359028119 29819410013072880538542179)
  ·
    refine ⟨44729115019609320807813269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29819410013072880538542179 44729115019609320807813269)
    ·
      refine ⟨2096677266544186912866247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44729115019609320807813269 2096677266544186912866247)
      ·
        refine ⟨3145015899816280369299371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096677266544186912866247 3145015899816280369299371)
        ·
          refine ⟨4717523849724420553949057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145015899816280369299371 4717523849724420553949057)
          ·
            refine ⟨3538142887293315415461793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717523849724420553949057 3538142887293315415461793)
            ·
              refine ⟨2653607165469986561596345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538142887293315415461793 2653607165469986561596345)
              ·
                refine ⟨1990205374102489921197259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653607165469986561596345 1990205374102489921197259)
                ·
                  refine ⟨2985308061153734881795889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990205374102489921197259 2985308061153734881795889)
                  ·
                    refine ⟨2238981045865301161346917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985308061153734881795889 2238981045865301161346917)
                    ·
                      refine ⟨419808946099743967752547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2238981045865301161346917 419808946099743967752547)
                      ·
                        rfl

theorem cell23_817575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_817575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817575 prefixEnd_817575 := by exact prefixLift 817575
  have htrace : WordTrace (prefixWord ++ tailWord_817575) baseStart_817575 baseEnd_817575 := by
    simpa [prefixWord, tailWord_817575, baseEnd_817575] using wordTrace_append hprefix tailTrace_817575
  have hstable : (prefixWord ++ tailWord_817575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817575).length < 2 ^ (prefixWord ++ tailWord_817575).sum := by decide
  have hdescent : baseEnd_817575 < baseStart_817575 := by decide
  rcases family_descends (prefixWord ++ tailWord_817575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817589 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_817589 : Nat := 118140960795 + 817589 * 2 ^ 59
def prefixEnd_817589 : Nat := 4983230072969 + 3 ^ 40 * 817589 * 2
def baseEnd_817589 : Nat := 139938711609635637659161

theorem tailTrace_817589 : CollatzResearch.WordTrace tailWord_817589 prefixEnd_817589 139938711609635637659161 := by
  unfold tailWord_817589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29819920635022160929551821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19879947090014773953034547 29819920635022160929551821)
  ·
    refine ⟨11182470238133310348581933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29819920635022160929551821 11182470238133310348581933)
    ·
      refine ⟨4193426339299991380718225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11182470238133310348581933 4193426339299991380718225)
      ·
        refine ⟨3145069754474993535538669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4193426339299991380718225 3145069754474993535538669)
        ·
          refine ⟨1179401157928122575827001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3145069754474993535538669 1179401157928122575827001)
          ·
            refine ⟨884550868446091931870251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179401157928122575827001 884550868446091931870251)
            ·
              refine ⟨1326826302669137897805377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884550868446091931870251 1326826302669137897805377)
              ·
                refine ⟨995119727001853423354033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326826302669137897805377 995119727001853423354033)
                ·
                  refine ⟨746339795251390067515525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995119727001853423354033 746339795251390067515525)
                  ·
                    refine ⟨139938711609635637659161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746339795251390067515525 139938711609635637659161)
                    ·
                      rfl

theorem cell23_817589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_817589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817589 prefixEnd_817589 := by exact prefixLift 817589
  have htrace : WordTrace (prefixWord ++ tailWord_817589) baseStart_817589 baseEnd_817589 := by
    simpa [prefixWord, tailWord_817589, baseEnd_817589] using wordTrace_append hprefix tailTrace_817589
  have hstable : (prefixWord ++ tailWord_817589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817589).length < 2 ^ (prefixWord ++ tailWord_817589).sum := by decide
  have hdescent : baseEnd_817589 < baseStart_817589 := by decide
  rcases family_descends (prefixWord ++ tailWord_817589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817596 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_817596 : Nat := 118140960795 + 817596 * 2 ^ 59
def prefixEnd_817596 : Nat := 4983230072969 + 3 ^ 40 * 817596 * 2
def baseEnd_817596 : Nat := 419819729193488385589951

theorem tailTrace_817596 : CollatzResearch.WordTrace tailWord_817596 prefixEnd_817596 419819729193488385589951 := by
  unfold tailWord_817596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910087972998400562528321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19880117297331200750037761 14910087972998400562528321)
  ·
    refine ⟨11182565979748800421896241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14910087972998400562528321 11182565979748800421896241)
    ·
      refine ⟨8386924484811600316422181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11182565979748800421896241 8386924484811600316422181)
      ·
        refine ⟨1572548340902175059329159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8386924484811600316422181 1572548340902175059329159)
        ·
          refine ⟨2358822511353262588993739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572548340902175059329159 2358822511353262588993739)
          ·
            refine ⟨3538233767029893883490609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358822511353262588993739 3538233767029893883490609)
            ·
              refine ⟨2653675325272420412617957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538233767029893883490609 2653675325272420412617957)
              ·
                refine ⟨497564123488578827365867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2653675325272420412617957 497564123488578827365867)
                ·
                  refine ⟨746346185232868241048801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497564123488578827365867 746346185232868241048801)
                  ·
                    refine ⟨559759638924651180786601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746346185232868241048801 559759638924651180786601)
                    ·
                      refine ⟨419819729193488385589951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559759638924651180786601 419819729193488385589951)
                      ·
                        rfl

theorem cell23_817596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_817596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817596 prefixEnd_817596 := by exact prefixLift 817596
  have htrace : WordTrace (prefixWord ++ tailWord_817596) baseStart_817596 baseEnd_817596 := by
    simpa [prefixWord, tailWord_817596, baseEnd_817596] using wordTrace_append hprefix tailTrace_817596
  have hstable : (prefixWord ++ tailWord_817596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817596).length < 2 ^ (prefixWord ++ tailWord_817596).sum := by decide
  have hdescent : baseEnd_817596 < baseStart_817596 := by decide
  rcases family_descends (prefixWord ++ tailWord_817596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817598 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_817598 : Nat := 118140960795 + 817598 * 2 ^ 59
def prefixEnd_817598 : Nat := 4983230072969 + 3 ^ 40 * 817598 * 2
def baseEnd_817598 : Nat := 139940252051599125921647

theorem tailTrace_817598 : CollatzResearch.WordTrace tailWord_817598 prefixEnd_817598 139940252051599125921647 := by
  unfold tailWord_817598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727531111498694433328681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19880165927993036977752965 3727531111498694433328681)
  ·
    refine ⟨2795648333624020824996511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3727531111498694433328681 2795648333624020824996511)
    ·
      refine ⟨4193472500436031237494767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795648333624020824996511 4193472500436031237494767)
      ·
        refine ⟨6290208750654046856242151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193472500436031237494767 6290208750654046856242151)
        ·
          refine ⟨9435313125981070284363227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290208750654046856242151 9435313125981070284363227)
          ·
            refine ⟨14152969688971605426544841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435313125981070284363227 14152969688971605426544841)
            ·
              refine ⟨10614727266728704069908631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14152969688971605426544841 10614727266728704069908631)
              ·
                refine ⟨15922090900093056104862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614727266728704069908631 15922090900093056104862947)
                ·
                  refine ⟨23883136350139584157294421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15922090900093056104862947 23883136350139584157294421)
                  ·
                    refine ⟨139940252051599125921647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23883136350139584157294421 139940252051599125921647)
                    ·
                      rfl

theorem cell23_817598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_817598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817598 prefixEnd_817598 := by exact prefixLift 817598
  have htrace : WordTrace (prefixWord ++ tailWord_817598) baseStart_817598 baseEnd_817598 := by
    simpa [prefixWord, tailWord_817598, baseEnd_817598] using wordTrace_append hprefix tailTrace_817598
  have hstable : (prefixWord ++ tailWord_817598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817598).length < 2 ^ (prefixWord ++ tailWord_817598).sum := by decide
  have hdescent : baseEnd_817598 < baseStart_817598 := by decide
  rcases family_descends (prefixWord ++ tailWord_817598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817658 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_817658 : Nat := 118140960795 + 817658 * 2 ^ 59
def prefixEnd_817658 : Nat := 4983230072969 + 3 ^ 40 * 817658 * 2
def baseEnd_817658 : Nat := 46650173888229682557185

theorem tailTrace_817658 : CollatzResearch.WordTrace tailWord_817658 prefixEnd_817658 46650173888229682557185 := by
  unfold tailWord_817658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455609317943046428453407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19881624847848123809209085 7455609317943046428453407)
  ·
    refine ⟨11183413976914569642680111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7455609317943046428453407 11183413976914569642680111)
    ·
      refine ⟨16775120965371854464020167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11183413976914569642680111 16775120965371854464020167)
      ·
        refine ⟨25162681448057781696030251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16775120965371854464020167 25162681448057781696030251)
        ·
          refine ⟨37744022172086672544045377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162681448057781696030251 37744022172086672544045377)
          ·
            refine ⟨28308016629065004408034033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37744022172086672544045377 28308016629065004408034033)
            ·
              refine ⟨21231012471798753306025525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28308016629065004408034033 21231012471798753306025525)
              ·
                refine ⟨1990407419231133122439893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21231012471798753306025525 1990407419231133122439893)
                ·
                  refine ⟨46650173888229682557185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1990407419231133122439893 46650173888229682557185)
                  ·
                    rfl

theorem cell23_817658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_817658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817658 prefixEnd_817658 := by exact prefixLift 817658
  have htrace : WordTrace (prefixWord ++ tailWord_817658) baseStart_817658 baseEnd_817658 := by
    simpa [prefixWord, tailWord_817658, baseEnd_817658] using wordTrace_append hprefix tailTrace_817658
  have hstable : (prefixWord ++ tailWord_817658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817658).length < 2 ^ (prefixWord ++ tailWord_817658).sum := by decide
  have hdescent : baseEnd_817658 < baseStart_817658 := by decide
  rcases family_descends (prefixWord ++ tailWord_817658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817742 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_817742 : Nat := 118140960795 + 817742 * 2 ^ 59
def prefixEnd_817742 : Nat := 4983230072969 + 3 ^ 40 * 817742 * 2
def baseEnd_817742 : Nat := 419894697369044814364279

theorem tailTrace_817742 : CollatzResearch.WordTrace tailWord_817742 prefixEnd_817742 419894697369044814364279 := by
  unfold tailWord_817742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728187625433483507483935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19883667335645245373247653 3728187625433483507483935)
  ·
    refine ⟨5592281438150225261225903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3728187625433483507483935 5592281438150225261225903)
    ·
      refine ⟨8388422157225337891838855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592281438150225261225903 8388422157225337891838855)
      ·
        refine ⟨12582633235838006837758283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388422157225337891838855 12582633235838006837758283)
        ·
          refine ⟨18873949853757010256637425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582633235838006837758283 18873949853757010256637425)
          ·
            refine ⟨14155462390317757692478069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18873949853757010256637425 14155462390317757692478069)
            ·
              refine ⟨1327074599092289783669819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14155462390317757692478069 1327074599092289783669819)
              ·
                refine ⟨1990611898638434675504729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327074599092289783669819 1990611898638434675504729)
                ·
                  refine ⟨1492958923978826006628547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990611898638434675504729 1492958923978826006628547)
                  ·
                    refine ⟨2239438385968239009942821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1492958923978826006628547 2239438385968239009942821)
                    ·
                      refine ⟨419894697369044814364279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2239438385968239009942821 419894697369044814364279)
                      ·
                        rfl

theorem cell23_817742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_817742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817742 prefixEnd_817742 := by exact prefixLift 817742
  have htrace : WordTrace (prefixWord ++ tailWord_817742) baseStart_817742 baseEnd_817742 := by
    simpa [prefixWord, tailWord_817742, baseEnd_817742] using wordTrace_append hprefix tailTrace_817742
  have hstable : (prefixWord ++ tailWord_817742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817742).length < 2 ^ (prefixWord ++ tailWord_817742).sum := by decide
  have hdescent : baseEnd_817742 < baseStart_817742 := by decide
  rcases family_descends (prefixWord ++ tailWord_817742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817795 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 3, 5]
def baseStart_817795 : Nat := 118140960795 + 817795 * 2 ^ 59
def prefixEnd_817795 : Nat := 4983230072969 + 3 ^ 40 * 817795 * 2
def baseEnd_817795 : Nat := 139973970614577702333845

theorem tailTrace_817795 : CollatzResearch.WordTrace tailWord_817795 prefixEnd_817795 139973970614577702333845 := by
  unfold tailWord_817795
  simp only [CollatzResearch.WordTrace]
  refine ⟨29827434072275858111550839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19884956048183905407700559 29827434072275858111550839)
  ·
    refine ⟨44741151108413787167326259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29827434072275858111550839 44741151108413787167326259)
    ·
      refine ⟨67111726662620680750989389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44741151108413787167326259 67111726662620680750989389)
      ·
        refine ⟨25166897498482755281621021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67111726662620680750989389 25166897498482755281621021)
        ·
          refine ⟨9437586561931033230607883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25166897498482755281621021 9437586561931033230607883)
          ·
            refine ⟨14156379842896549845911825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437586561931033230607883 14156379842896549845911825)
            ·
              refine ⟨10617284882172412384433869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14156379842896549845911825 10617284882172412384433869)
              ·
                refine ⟨3981481830814654644162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10617284882172412384433869 3981481830814654644162701)
                ·
                  refine ⟨1493055686555495491561013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3981481830814654644162701 1493055686555495491561013)
                  ·
                    refine ⟨139973970614577702333845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1493055686555495491561013 139973970614577702333845)
                    ·
                      rfl

theorem cell23_817795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].length) (baseStart_817795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817795 prefixEnd_817795 := by exact prefixLift 817795
  have htrace : WordTrace (prefixWord ++ tailWord_817795) baseStart_817795 baseEnd_817795 := by
    simpa [prefixWord, tailWord_817795, baseEnd_817795] using wordTrace_append hprefix tailTrace_817795
  have hstable : (prefixWord ++ tailWord_817795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817795).length < 2 ^ (prefixWord ++ tailWord_817795).sum := by decide
  have hdescent : baseEnd_817795 < baseStart_817795 := by decide
  rcases family_descends (prefixWord ++ tailWord_817795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817846 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_817846 : Nat := 118140960795 + 817846 * 2 ^ 59
def prefixEnd_817846 : Nat := 4983230072969 + 3 ^ 40 * 817846 * 2
def baseEnd_817846 : Nat := 139982699785704135821267

theorem tailTrace_817846 : CollatzResearch.WordTrace tailWord_817846 prefixEnd_817846 139982699785704135821267 := by
  unfold tailWord_817846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864330887193193363853587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19886196130060729214438261 1864330887193193363853587)
  ·
    refine ⟨2796496330789790045780381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864330887193193363853587 2796496330789790045780381)
    ·
      refine ⟨1048686124046171267167643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2796496330789790045780381 1048686124046171267167643)
      ·
        refine ⟨1573029186069256900751465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048686124046171267167643 1573029186069256900751465)
        ·
          refine ⟨1179771889551942675563599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573029186069256900751465 1179771889551942675563599)
          ·
            refine ⟨1769657834327914013345399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179771889551942675563599 1769657834327914013345399)
            ·
              refine ⟨2654486751491871020018099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769657834327914013345399 2654486751491871020018099)
              ·
                refine ⟨3981730127237806530027149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654486751491871020018099 3981730127237806530027149)
                ·
                  refine ⟨1493148797714177448760181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3981730127237806530027149 1493148797714177448760181)
                  ·
                    refine ⟨139982699785704135821267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1493148797714177448760181 139982699785704135821267)
                    ·
                      rfl

theorem cell23_817846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_817846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817846 prefixEnd_817846 := by exact prefixLift 817846
  have htrace : WordTrace (prefixWord ++ tailWord_817846) baseStart_817846 baseEnd_817846 := by
    simpa [prefixWord, tailWord_817846, baseEnd_817846] using wordTrace_append hprefix tailTrace_817846
  have hstable : (prefixWord ++ tailWord_817846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817846).length < 2 ^ (prefixWord ++ tailWord_817846).sum := by decide
  have hdescent : baseEnd_817846 < baseStart_817846 := by decide
  rcases family_descends (prefixWord ++ tailWord_817846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817849 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 5, 2, 2]
def baseStart_817849 : Nat := 118140960795 + 817849 * 2 ^ 59
def prefixEnd_817849 : Nat := 4983230072969 + 3 ^ 40 * 817849 * 2
def baseEnd_817849 : Nat := 419949639799075895726287

theorem tailTrace_817849 : CollatzResearch.WordTrace tailWord_817849 prefixEnd_817849 419949639799075895726287 := by
  unfold tailWord_817849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829403614080225334016601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19886269076053483556011067 29829403614080225334016601)
  ·
    refine ⟨22372052710560169000512451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29829403614080225334016601 22372052710560169000512451)
    ·
      refine ⟨33558079065840253500768677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22372052710560169000512451 33558079065840253500768677)
      ·
        refine ⟨6292139824845047531394127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33558079065840253500768677 6292139824845047531394127)
        ·
          refine ⟨9438209737267571297091191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292139824845047531394127 9438209737267571297091191)
          ·
            refine ⟨14157314605901356945636787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438209737267571297091191 14157314605901356945636787)
            ·
              refine ⟨21235971908852035418455181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157314605901356945636787 21235971908852035418455181)
              ·
                refine ⟨7963489465819513281920693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21235971908852035418455181 7963489465819513281920693)
                ·
                  refine ⟨746577137420579370180065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7963489465819513281920693 746577137420579370180065)
                  ·
                    refine ⟨559932853065434527635049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746577137420579370180065 559932853065434527635049)
                    ·
                      refine ⟨419949639799075895726287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559932853065434527635049 419949639799075895726287)
                      ·
                        rfl

theorem cell23_817849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_817849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817849 prefixEnd_817849 := by exact prefixLift 817849
  have htrace : WordTrace (prefixWord ++ tailWord_817849) baseStart_817849 baseEnd_817849 := by
    simpa [prefixWord, tailWord_817849, baseEnd_817849] using wordTrace_append hprefix tailTrace_817849
  have hstable : (prefixWord ++ tailWord_817849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817849).length < 2 ^ (prefixWord ++ tailWord_817849).sum := by decide
  have hdescent : baseEnd_817849 < baseStart_817849 := by decide
  rcases family_descends (prefixWord ++ tailWord_817849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817855 : List Nat := [1, 1, 2, 2, 2, 4, 2, 9]
def baseStart_817855 : Nat := 118140960795 + 817855 * 2 ^ 59
def prefixEnd_817855 : Nat := 4983230072969 + 3 ^ 40 * 817855 * 2
def baseEnd_817855 : Nat := 15553804469740847120417

theorem tailTrace_817855 : CollatzResearch.WordTrace tailWord_817855 prefixEnd_817855 15553804469740847120417 := by
  unfold tailWord_817855
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829622452058488358735019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19886414968038992239156679 29829622452058488358735019)
  ·
    refine ⟨44744433678087732538102529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29829622452058488358735019 44744433678087732538102529)
    ·
      refine ⟨33558325258565799403576897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44744433678087732538102529 33558325258565799403576897)
      ·
        refine ⟨25168743943924349552682673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33558325258565799403576897 25168743943924349552682673)
        ·
          refine ⟨18876557957943262164512005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25168743943924349552682673 18876557957943262164512005)
          ·
            refine ⟨3539354617114361655846001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18876557957943262164512005 3539354617114361655846001)
            ·
              refine ⟨2654515962835771241884501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539354617114361655846001 2654515962835771241884501)
              ·
                refine ⟨15553804469740847120417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2654515962835771241884501 15553804469740847120417)
                ·
                  rfl

theorem cell23_817855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 9].length) (baseStart_817855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817855 prefixEnd_817855 := by exact prefixLift 817855
  have htrace : WordTrace (prefixWord ++ tailWord_817855) baseStart_817855 baseEnd_817855 := by
    simpa [prefixWord, tailWord_817855, baseEnd_817855] using wordTrace_append hprefix tailTrace_817855
  have hstable : (prefixWord ++ tailWord_817855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817855).length < 2 ^ (prefixWord ++ tailWord_817855).sum := by decide
  have hdescent : baseEnd_817855 < baseStart_817855 := by decide
  rcases family_descends (prefixWord ++ tailWord_817855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817866 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_817866 : Nat := 118140960795 + 817866 * 2 ^ 59
def prefixEnd_817866 : Nat := 4983230072969 + 3 ^ 40 * 817866 * 2
def baseEnd_817866 : Nat := 419958368970202329213709

theorem tailTrace_817866 : CollatzResearch.WordTrace tailWord_817866 prefixEnd_817866 419958368970202329213709 := by
  unfold tailWord_817866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457505913754659309346363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19886682436679091491590301 7457505913754659309346363)
  ·
    refine ⟨11186258870631988964019545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7457505913754659309346363 11186258870631988964019545)
    ·
      refine ⟨8389694152973991723014659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11186258870631988964019545 8389694152973991723014659)
      ·
        refine ⟨12584541229460987584521989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389694152973991723014659 12584541229460987584521989)
        ·
          refine ⟨2359601480523935172097873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12584541229460987584521989 2359601480523935172097873)
          ·
            refine ⟨1769701110392951379073405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359601480523935172097873 1769701110392951379073405)
            ·
              refine ⟨663637916397356767152527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769701110392951379073405 663637916397356767152527)
              ·
                refine ⟨995456874596035150728791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663637916397356767152527 995456874596035150728791)
                ·
                  refine ⟨1493185311894052726093187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995456874596035150728791 1493185311894052726093187)
                  ·
                    refine ⟨2239777967841079089139781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493185311894052726093187 2239777967841079089139781)
                    ·
                      refine ⟨419958368970202329213709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2239777967841079089139781 419958368970202329213709)
                      ·
                        rfl

theorem cell23_817866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_817866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817866 prefixEnd_817866 := by exact prefixLift 817866
  have htrace : WordTrace (prefixWord ++ tailWord_817866) baseStart_817866 baseEnd_817866 := by
    simpa [prefixWord, tailWord_817866, baseEnd_817866] using wordTrace_append hprefix tailTrace_817866
  have hstable : (prefixWord ++ tailWord_817866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817866).length < 2 ^ (prefixWord ++ tailWord_817866).sum := by decide
  have hdescent : baseEnd_817866 < baseStart_817866 := by decide
  rcases family_descends (prefixWord ++ tailWord_817866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817877 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_817877 : Nat := 118140960795 + 817877 * 2 ^ 59
def prefixEnd_817877 : Nat := 4983230072969 + 3 ^ 40 * 817877 * 2
def baseEnd_817877 : Nat := 419964017257401786176159

theorem tailTrace_817877 : CollatzResearch.WordTrace tailWord_817877 prefixEnd_817877 419964017257401786176159 := by
  unfold tailWord_817877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830424857978786116035885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19886949905319190744023923 29830424857978786116035885)
  ·
    refine ⟨11186409321742044793513457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29830424857978786116035885 11186409321742044793513457)
    ·
      refine ⟨8389806991306533595135093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11186409321742044793513457 8389806991306533595135093)
      ·
        refine ⟨786544405434987524543915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8389806991306533595135093 786544405434987524543915)
        ·
          refine ⟨1179816608152481286815873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786544405434987524543915 1179816608152481286815873)
          ·
            refine ⟨884862456114360965111905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179816608152481286815873 884862456114360965111905)
            ·
              refine ⟨663646842085770723833929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884862456114360965111905 663646842085770723833929)
              ·
                refine ⟨497735131564328042875447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663646842085770723833929 497735131564328042875447)
                ·
                  refine ⟨746602697346492064313171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497735131564328042875447 746602697346492064313171)
                  ·
                    refine ⟨1119904046019738096469757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746602697346492064313171 1119904046019738096469757)
                    ·
                      refine ⟨419964017257401786176159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1119904046019738096469757 419964017257401786176159)
                      ·
                        rfl

theorem cell23_817877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_817877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817877 prefixEnd_817877 := by exact prefixLift 817877
  have htrace : WordTrace (prefixWord ++ tailWord_817877) baseStart_817877 baseEnd_817877 := by
    simpa [prefixWord, tailWord_817877, baseEnd_817877] using wordTrace_append hprefix tailTrace_817877
  have hstable : (prefixWord ++ tailWord_817877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817877).length < 2 ^ (prefixWord ++ tailWord_817877).sum := by decide
  have hdescent : baseEnd_817877 < baseStart_817877 := by decide
  rcases family_descends (prefixWord ++ tailWord_817877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817882 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_817882 : Nat := 118140960795 + 817882 * 2 ^ 59
def prefixEnd_817882 : Nat := 4983230072969 + 3 ^ 40 * 817882 * 2
def baseEnd_817882 : Nat := 419966584660674266613635

theorem tailTrace_817882 : CollatzResearch.WordTrace tailWord_817882 prefixEnd_817882 419966584660674266613635 := by
  unfold tailWord_817882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457651805740167992491975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19887071481973781313311933 7457651805740167992491975)
  ·
    refine ⟨11186477708610251988737963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7457651805740167992491975 11186477708610251988737963)
    ·
      refine ⟨16779716562915377983106945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11186477708610251988737963 16779716562915377983106945)
      ·
        refine ⟨12584787422186533487330209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16779716562915377983106945 12584787422186533487330209)
        ·
          refine ⟨9438590566639900115497657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12584787422186533487330209 9438590566639900115497657)
          ·
            refine ⟨7078942924979925086623243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438590566639900115497657 7078942924979925086623243)
            ·
              refine ⟨10618414387469887629934865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078942924979925086623243 10618414387469887629934865)
              ·
                refine ⟨7963810790602415722451149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10618414387469887629934865 7963810790602415722451149)
                ·
                  refine ⟨2986429046475905895919181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7963810790602415722451149 2986429046475905895919181)
                  ·
                    refine ⟨1119910892428464710969693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986429046475905895919181 1119910892428464710969693)
                    ·
                      refine ⟨419966584660674266613635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1119910892428464710969693 419966584660674266613635)
                      ·
                        rfl

theorem cell23_817882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_817882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_817882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_817882 prefixEnd_817882 := by exact prefixLift 817882
  have htrace : WordTrace (prefixWord ++ tailWord_817882) baseStart_817882 baseEnd_817882 := by
    simpa [prefixWord, tailWord_817882, baseEnd_817882] using wordTrace_append hprefix tailTrace_817882
  have hstable : (prefixWord ++ tailWord_817882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817882).length < 2 ^ (prefixWord ++ tailWord_817882).sum := by decide
  have hdescent : baseEnd_817882 < baseStart_817882 := by decide
  rcases family_descends (prefixWord ++ tailWord_817882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818042 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_818042 : Nat := 118140960795 + 818042 * 2 ^ 59
def prefixEnd_818042 : Nat := 4983230072969 + 3 ^ 40 * 818042 * 2
def baseEnd_818042 : Nat := 420048741565393640612899

theorem tailTrace_818042 : CollatzResearch.WordTrace tailWord_818042 prefixEnd_818042 420048741565393640612899 := by
  unfold tailWord_818042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459110725595254823948095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19890961934920679530528253 7459110725595254823948095)
  ·
    refine ⟨11188666088392882235922143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459110725595254823948095 11188666088392882235922143)
    ·
      refine ⟨16782999132589323353883215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11188666088392882235922143 16782999132589323353883215)
      ·
        refine ⟨25174498698883985030824823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782999132589323353883215 25174498698883985030824823)
        ·
          refine ⟨37761748048325977546237235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25174498698883985030824823 37761748048325977546237235)
          ·
            refine ⟨56642622072488966319355853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37761748048325977546237235 56642622072488966319355853)
            ·
              refine ⟨21240983277183362369758445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56642622072488966319355853 21240983277183362369758445)
              ·
                refine ⟨7965368728943760888659417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21240983277183362369758445 7965368728943760888659417)
                ·
                  refine ⟨5974026546707820666494563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965368728943760888659417 5974026546707820666494563)
                  ·
                    refine ⟨8961039820061730999741845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974026546707820666494563 8961039820061730999741845)
                    ·
                      refine ⟨420048741565393640612899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8961039820061730999741845 420048741565393640612899)
                      ·
                        rfl

theorem cell23_818042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_818042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818042 prefixEnd_818042 := by exact prefixLift 818042
  have htrace : WordTrace (prefixWord ++ tailWord_818042) baseStart_818042 baseEnd_818042 := by
    simpa [prefixWord, tailWord_818042, baseEnd_818042] using wordTrace_append hprefix tailTrace_818042
  have hstable : (prefixWord ++ tailWord_818042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818042).length < 2 ^ (prefixWord ++ tailWord_818042).sum := by decide
  have hdescent : baseEnd_818042 < baseStart_818042 := by decide
  rcases family_descends (prefixWord ++ tailWord_818042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818069 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 6]
def baseStart_818069 : Nat := 118140960795 + 818069 * 2 ^ 59
def prefixEnd_818069 : Nat := 4983230072969 + 3 ^ 40 * 818069 * 2
def baseEnd_818069 : Nat := 46673622838118337219475

theorem tailTrace_818069 : CollatzResearch.WordTrace tailWord_818069 prefixEnd_818069 46673622838118337219475 := by
  unfold tailWord_818069
  simp only [CollatzResearch.WordTrace]
  refine ⟨29837427673283202907025261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19891618448855468604683507 29837427673283202907025261)
  ·
    refine ⟨11189035377481201090134473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29837427673283202907025261 11189035377481201090134473)
    ·
      refine ⟨8391776533110900817600855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11189035377481201090134473 8391776533110900817600855)
      ·
        refine ⟨12587664799666351226401283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8391776533110900817600855 12587664799666351226401283)
        ·
          refine ⟨18881497199499526839601925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12587664799666351226401283 18881497199499526839601925)
          ·
            refine ⟨3540280724906161282425361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18881497199499526839601925 3540280724906161282425361)
            ·
              refine ⟨2655210543679620961819021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540280724906161282425361 2655210543679620961819021)
              ·
                refine ⟨995703953879857860682133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2655210543679620961819021 995703953879857860682133)
                ·
                  refine ⟨46673622838118337219475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 995703953879857860682133 46673622838118337219475)
                  ·
                    rfl

theorem cell23_818069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_818069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818069 prefixEnd_818069 := by exact prefixLift 818069
  have htrace : WordTrace (prefixWord ++ tailWord_818069) baseStart_818069 baseEnd_818069 := by
    simpa [prefixWord, tailWord_818069, baseEnd_818069] using wordTrace_append hprefix tailTrace_818069
  have hstable : (prefixWord ++ tailWord_818069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818069).length < 2 ^ (prefixWord ++ tailWord_818069).sum := by decide
  have hdescent : baseEnd_818069 < baseStart_818069 := by decide
  rcases family_descends (prefixWord ++ tailWord_818069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818092 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_818092 : Nat := 118140960795 + 818092 * 2 ^ 59
def prefixEnd_818092 : Nat := 4983230072969 + 3 ^ 40 * 818092 * 2
def baseEnd_818092 : Nat := 420074415598118444987669

theorem tailTrace_818092 : CollatzResearch.WordTrace tailWord_818092 prefixEnd_818092 420074415598118444987669 := by
  unfold tailWord_818092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919133276099938917556265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19892177701466585223408353 14919133276099938917556265)
  ·
    refine ⟨11189349957074954188167199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14919133276099938917556265 11189349957074954188167199)
    ·
      refine ⟨16784024935612431282250799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189349957074954188167199 16784024935612431282250799)
      ·
        refine ⟨25176037403418646923376199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16784024935612431282250799 25176037403418646923376199)
        ·
          refine ⟨37764056105127970385064299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176037403418646923376199 37764056105127970385064299)
          ·
            refine ⟨56646084157691955577596449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37764056105127970385064299 56646084157691955577596449)
            ·
              refine ⟨42484563118268966683197337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56646084157691955577596449 42484563118268966683197337)
              ·
                refine ⟨31863422338701725012398003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42484563118268966683197337 31863422338701725012398003)
                ·
                  refine ⟨47795133508052587518597005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31863422338701725012398003 47795133508052587518597005)
                  ·
                    refine ⟨17923175065519720319473877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47795133508052587518597005 17923175065519720319473877)
                    ·
                      refine ⟨420074415598118444987669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17923175065519720319473877 420074415598118444987669)
                      ·
                        rfl

theorem cell23_818092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_818092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818092 prefixEnd_818092 := by exact prefixLift 818092
  have htrace : WordTrace (prefixWord ++ tailWord_818092) baseStart_818092 baseEnd_818092 := by
    simpa [prefixWord, tailWord_818092, baseEnd_818092] using wordTrace_append hprefix tailTrace_818092
  have hstable : (prefixWord ++ tailWord_818092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818092).length < 2 ^ (prefixWord ++ tailWord_818092).sum := by decide
  have hdescent : baseEnd_818092 < baseStart_818092 := by decide
  rcases family_descends (prefixWord ++ tailWord_818092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818106 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_818106 : Nat := 118140960795 + 818106 * 2 ^ 59
def prefixEnd_818106 : Nat := 4983230072969 + 3 ^ 40 * 818106 * 2
def baseEnd_818106 : Nat := 420081604327281390212605

theorem tailTrace_818106 : CollatzResearch.WordTrace tailWord_818106 prefixEnd_818106 420081604327281390212605 := by
  unfold tailWord_818106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459694293537289556530543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19892518116099438817414781 7459694293537289556530543)
  ·
    refine ⟨11189541440305934334795815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459694293537289556530543 11189541440305934334795815)
    ·
      refine ⟨16784312160458901502193723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189541440305934334795815 16784312160458901502193723)
      ·
        refine ⟨25176468240688352253290585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16784312160458901502193723 25176468240688352253290585)
        ·
          refine ⟨18882351180516264189967939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25176468240688352253290585 18882351180516264189967939)
          ·
            refine ⟨28323526770774396284951909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18882351180516264189967939 28323526770774396284951909)
            ·
              refine ⟨5310661269520199303428483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28323526770774396284951909 5310661269520199303428483)
              ·
                refine ⟨7965991904280298955142725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310661269520199303428483 7965991904280298955142725)
                ·
                  refine ⟨1493623482052556054089261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7965991904280298955142725 1493623482052556054089261)
                  ·
                    refine ⟨560108805769708520283473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493623482052556054089261 560108805769708520283473)
                    ·
                      refine ⟨420081604327281390212605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560108805769708520283473 420081604327281390212605)
                      ·
                        rfl

theorem cell23_818106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_818106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818106 prefixEnd_818106 := by exact prefixLift 818106
  have htrace : WordTrace (prefixWord ++ tailWord_818106) baseStart_818106 baseEnd_818106 := by
    simpa [prefixWord, tailWord_818106, baseEnd_818106] using wordTrace_append hprefix tailTrace_818106
  have hstable : (prefixWord ++ tailWord_818106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818106).length < 2 ^ (prefixWord ++ tailWord_818106).sum := by decide
  have hdescent : baseEnd_818106 < baseStart_818106 := by decide
  rcases family_descends (prefixWord ++ tailWord_818106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818119 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_818119 : Nat := 118140960795 + 818119 * 2 ^ 59
def prefixEnd_818119 : Nat := 4983230072969 + 3 ^ 40 * 818119 * 2
def baseEnd_818119 : Nat := 420088279575789839350045

theorem tailTrace_818119 : CollatzResearch.WordTrace tailWord_818119 prefixEnd_818119 420088279575789839350045 := by
  unfold tailWord_818119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29839251323102061446345411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19892834215401374297563607 29839251323102061446345411)
  ·
    refine ⟨44758876984653092169518117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29839251323102061446345411 44758876984653092169518117)
    ·
      refine ⟨8392289434622454781784647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44758876984653092169518117 8392289434622454781784647)
      ·
        refine ⟨12588434151933682172676971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8392289434622454781784647 12588434151933682172676971)
        ·
          refine ⟨18882651227900523259015457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588434151933682172676971 18882651227900523259015457)
          ·
            refine ⟨14161988420925392444261593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18882651227900523259015457 14161988420925392444261593)
            ·
              refine ⟨10621491315694044333196195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14161988420925392444261593 10621491315694044333196195)
              ·
                refine ⟨15932236973541066499794293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621491315694044333196195 15932236973541066499794293)
                ·
                  refine ⟨1493647216269474984355715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15932236973541066499794293 1493647216269474984355715)
                  ·
                    refine ⟨2240470824404212476533573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493647216269474984355715 2240470824404212476533573)
                    ·
                      refine ⟨420088279575789839350045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2240470824404212476533573 420088279575789839350045)
                      ·
                        rfl

theorem cell23_818119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_818119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818119 prefixEnd_818119 := by exact prefixLift 818119
  have htrace : WordTrace (prefixWord ++ tailWord_818119) baseStart_818119 baseEnd_818119 := by
    simpa [prefixWord, tailWord_818119, baseEnd_818119] using wordTrace_append hprefix tailTrace_818119
  have hstable : (prefixWord ++ tailWord_818119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818119).length < 2 ^ (prefixWord ++ tailWord_818119).sum := by decide
  have hdescent : baseEnd_818119 < baseStart_818119 := by decide
  rcases family_descends (prefixWord ++ tailWord_818119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818133 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_818133 : Nat := 118140960795 + 818133 * 2 ^ 59
def prefixEnd_818133 : Nat := 4983230072969 + 3 ^ 40 * 818133 * 2
def baseEnd_818133 : Nat := 140031822768317594858327

theorem tailTrace_818133 : CollatzResearch.WordTrace tailWord_818133 prefixEnd_818133 140031822768317594858327 := by
  unfold tailWord_818133
  simp only [CollatzResearch.WordTrace]
  refine ⟨29839761945051341837355053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19893174630034227891570035 29839761945051341837355053)
  ·
    refine ⟨11189910729394253189008145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29839761945051341837355053 11189910729394253189008145)
    ·
      refine ⟨8392433047045689891756109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11189910729394253189008145 8392433047045689891756109)
      ·
        refine ⟨3147162392642133709408541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8392433047045689891756109 3147162392642133709408541)
        ·
          refine ⟨1180185897240800141028203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3147162392642133709408541 1180185897240800141028203)
          ·
            refine ⟨1770278845861200211542305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180185897240800141028203 1770278845861200211542305)
            ·
              refine ⟨1327709134395900158656729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770278845861200211542305 1327709134395900158656729)
              ·
                refine ⟨995781850796925118992547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327709134395900158656729 995781850796925118992547)
                ·
                  refine ⟨1493672776195387678488821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995781850796925118992547 1493672776195387678488821)
                  ·
                    refine ⟨140031822768317594858327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1493672776195387678488821 140031822768317594858327)
                    ·
                      rfl

theorem cell23_818133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_818133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818133 prefixEnd_818133 := by exact prefixLift 818133
  have htrace : WordTrace (prefixWord ++ tailWord_818133) baseStart_818133 baseEnd_818133 := by
    simpa [prefixWord, tailWord_818133, baseEnd_818133] using wordTrace_append hprefix tailTrace_818133
  have hstable : (prefixWord ++ tailWord_818133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818133).length < 2 ^ (prefixWord ++ tailWord_818133).sum := by decide
  have hdescent : baseEnd_818133 < baseStart_818133 := by decide
  rcases family_descends (prefixWord ++ tailWord_818133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818136 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_818136 : Nat := 118140960795 + 818136 * 2 ^ 59
def prefixEnd_818136 : Nat := 4983230072969 + 3 ^ 40 * 818136 * 2
def baseEnd_818136 : Nat := 420097008746916272837467

theorem tailTrace_818136 : CollatzResearch.WordTrace tailWord_818136 prefixEnd_818136 420097008746916272837467 := by
  unfold tailWord_818136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919935682020236674857131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19893247576026982233142841 14919935682020236674857131)
  ·
    refine ⟨22379903523030355012285697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14919935682020236674857131 22379903523030355012285697)
    ·
      refine ⟨16784927642272766259214273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22379903523030355012285697 16784927642272766259214273)
      ·
        refine ⟨12588695731704574694410705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784927642272766259214273 12588695731704574694410705)
        ·
          refine ⟨9441521798778431020808029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12588695731704574694410705 9441521798778431020808029)
          ·
            refine ⟨3540570674541911632803011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9441521798778431020808029 3540570674541911632803011)
            ·
              refine ⟨5310856011812867449204517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540570674541911632803011 5310856011812867449204517)
              ·
                refine ⟨995785502214912646725847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5310856011812867449204517 995785502214912646725847)
                ·
                  refine ⟨1493678253322368970088771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995785502214912646725847 1493678253322368970088771)
                  ·
                    refine ⟨2240517379983553455133157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493678253322368970088771 2240517379983553455133157)
                    ·
                      refine ⟨420097008746916272837467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2240517379983553455133157 420097008746916272837467)
                      ·
                        rfl

theorem cell23_818136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_818136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818136 prefixEnd_818136 := by exact prefixLift 818136
  have htrace : WordTrace (prefixWord ++ tailWord_818136) baseStart_818136 baseEnd_818136 := by
    simpa [prefixWord, tailWord_818136, baseEnd_818136] using wordTrace_append hprefix tailTrace_818136
  have hstable : (prefixWord ++ tailWord_818136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818136).length < 2 ^ (prefixWord ++ tailWord_818136).sum := by decide
  have hdescent : baseEnd_818136 < baseStart_818136 := by decide
  rcases family_descends (prefixWord ++ tailWord_818136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818159 : List Nat := [1, 1, 2, 1, 4, 5, 9]
def baseStart_818159 : Nat := 118140960795 + 818159 * 2 ^ 59
def prefixEnd_818159 : Nat := 4983230072969 + 3 ^ 40 * 818159 * 2
def baseEnd_818159 : Nat := 5186528627184810899381

theorem tailTrace_818159 : CollatzResearch.WordTrace tailWord_818159 prefixEnd_818159 5186528627184810899381 := by
  unfold tailWord_818159
  simp only [CollatzResearch.WordTrace]
  refine ⟨29840710242957148277801531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19893806828638098851867687 29840710242957148277801531)
  ·
    refine ⟨44761065364435722416702297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29840710242957148277801531 44761065364435722416702297)
    ·
      refine ⟨33570799023326791812526723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44761065364435722416702297 33570799023326791812526723)
      ·
        refine ⟨50356198534990187718790085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33570799023326791812526723 50356198534990187718790085)
        ·
          refine ⟨9441787225310660197273141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50356198534990187718790085 9441787225310660197273141)
          ·
            refine ⟨885167552372874393494357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9441787225310660197273141 885167552372874393494357)
            ·
              refine ⟨5186528627184810899381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 885167552372874393494357 5186528627184810899381)
              ·
                rfl

theorem cell23_818159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 9].length) (baseStart_818159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818159 prefixEnd_818159 := by exact prefixLift 818159
  have htrace : WordTrace (prefixWord ++ tailWord_818159) baseStart_818159 baseEnd_818159 := by
    simpa [prefixWord, tailWord_818159, baseEnd_818159] using wordTrace_append hprefix tailTrace_818159
  have hstable : (prefixWord ++ tailWord_818159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818159).length < 2 ^ (prefixWord ++ tailWord_818159).sum := by decide
  have hdescent : baseEnd_818159 < baseStart_818159 := by decide
  rcases family_descends (prefixWord ++ tailWord_818159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818166 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_818166 : Nat := 118140960795 + 818166 * 2 ^ 59
def prefixEnd_818166 : Nat := 4983230072969 + 3 ^ 40 * 818166 * 2
def baseEnd_818166 : Nat := 420112413166551155462329

theorem tailTrace_818166 : CollatzResearch.WordTrace tailWord_818166 prefixEnd_818166 420112413166551155462329 := by
  unfold tailWord_818166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865060347120736779581647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19893977035954525648870901 1865060347120736779581647)
  ·
    refine ⟨2797590520681105169372471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865060347120736779581647 2797590520681105169372471)
    ·
      refine ⟨4196385781021657754058707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797590520681105169372471 4196385781021657754058707)
      ·
        refine ⟨6294578671532486631088061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196385781021657754058707 6294578671532486631088061)
        ·
          refine ⟨2360467001824682486658023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6294578671532486631088061 2360467001824682486658023)
          ·
            refine ⟨3540700502737023729987035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360467001824682486658023 3540700502737023729987035)
            ·
              refine ⟨5311050754105535594980553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540700502737023729987035 5311050754105535594980553)
              ·
                refine ⟨3983288065579151696235415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311050754105535594980553 3983288065579151696235415)
                ·
                  refine ⟨5974932098368727544353123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983288065579151696235415 5974932098368727544353123)
                  ·
                    refine ⟨8962398147553091316529685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974932098368727544353123 8962398147553091316529685)
                    ·
                      refine ⟨420112413166551155462329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8962398147553091316529685 420112413166551155462329)
                      ·
                        rfl

theorem cell23_818166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_818166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818166 prefixEnd_818166 := by exact prefixLift 818166
  have htrace : WordTrace (prefixWord ++ tailWord_818166) baseStart_818166 baseEnd_818166 := by
    simpa [prefixWord, tailWord_818166, baseEnd_818166] using wordTrace_append hprefix tailTrace_818166
  have hstable : (prefixWord ++ tailWord_818166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818166).length < 2 ^ (prefixWord ++ tailWord_818166).sum := by decide
  have hdescent : baseEnd_818166 < baseStart_818166 := by decide
  rcases family_descends (prefixWord ++ tailWord_818166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818170 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_818170 : Nat := 118140960795 + 818170 * 2 ^ 59
def prefixEnd_818170 : Nat := 4983230072969 + 3 ^ 40 * 818170 * 2
def baseEnd_818170 : Nat := 420114467089169139812311

theorem tailTrace_818170 : CollatzResearch.WordTrace tailWord_818170 prefixEnd_818170 420114467089169139812311 := by
  unfold tailWord_818170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460277861479324289112991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19894074297278198104301309 7460277861479324289112991)
  ·
    refine ⟨11190416792218986433669487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7460277861479324289112991 11190416792218986433669487)
    ·
      refine ⟨16785625188328479650504231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11190416792218986433669487 16785625188328479650504231)
      ·
        refine ⟨25178437782492719475756347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16785625188328479650504231 25178437782492719475756347)
        ·
          refine ⟨37767656673739079213634521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25178437782492719475756347 37767656673739079213634521)
          ·
            refine ⟨28325742505304309410225891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37767656673739079213634521 28325742505304309410225891)
            ·
              refine ⟨42488613757956464115338837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28325742505304309410225891 42488613757956464115338837)
              ·
                refine ⟨497913442476052313851627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42488613757956464115338837 497913442476052313851627)
                ·
                  refine ⟨746870163714078470777441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497913442476052313851627 746870163714078470777441)
                  ·
                    refine ⟨560152622785558853083081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746870163714078470777441 560152622785558853083081)
                    ·
                      refine ⟨420114467089169139812311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560152622785558853083081 420114467089169139812311)
                      ·
                        rfl

theorem cell23_818170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_818170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818170 prefixEnd_818170 := by exact prefixLift 818170
  have htrace : WordTrace (prefixWord ++ tailWord_818170) baseStart_818170 baseEnd_818170 := by
    simpa [prefixWord, tailWord_818170, baseEnd_818170] using wordTrace_append hprefix tailTrace_818170
  have hstable : (prefixWord ++ tailWord_818170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818170).length < 2 ^ (prefixWord ++ tailWord_818170).sum := by decide
  have hdescent : baseEnd_818170 < baseStart_818170 := by decide
  rcases family_descends (prefixWord ++ tailWord_818170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818190 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_818190 : Nat := 118140960795 + 818190 * 2 ^ 59
def prefixEnd_818190 : Nat := 4983230072969 + 3 ^ 40 * 818190 * 2
def baseEnd_818190 : Nat := 420124736702259061562219

theorem tailTrace_818190 : CollatzResearch.WordTrace tailWord_818190 prefixEnd_818190 420124736702259061562219 := by
  unfold tailWord_818190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730230113230605071522503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19894560603896560381453349 3730230113230605071522503)
  ·
    refine ⟨5595345169845907607283755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730230113230605071522503 5595345169845907607283755)
    ·
      refine ⟨8393017754768861410925633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595345169845907607283755 8393017754768861410925633)
      ·
        refine ⟨6294763316076646058194225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8393017754768861410925633 6294763316076646058194225)
        ·
          refine ⟨4721072487057484543645669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6294763316076646058194225 4721072487057484543645669)
          ·
            refine ⟨885201091323278351933563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4721072487057484543645669 885201091323278351933563)
            ·
              refine ⟨1327801636984917527900345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885201091323278351933563 1327801636984917527900345)
              ·
                refine ⟨995851227738688145925259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327801636984917527900345 995851227738688145925259)
                ·
                  refine ⟨1493776841608032218887889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995851227738688145925259 1493776841608032218887889)
                  ·
                    refine ⟨1120332631206024164165917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1493776841608032218887889 1120332631206024164165917)
                    ·
                      refine ⟨420124736702259061562219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120332631206024164165917 420124736702259061562219)
                      ·
                        rfl

theorem cell23_818190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_818190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818190 prefixEnd_818190 := by exact prefixLift 818190
  have htrace : WordTrace (prefixWord ++ tailWord_818190) baseStart_818190 baseEnd_818190 := by
    simpa [prefixWord, tailWord_818190, baseEnd_818190] using wordTrace_append hprefix tailTrace_818190
  have hstable : (prefixWord ++ tailWord_818190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818190).length < 2 ^ (prefixWord ++ tailWord_818190).sum := by decide
  have hdescent : baseEnd_818190 < baseStart_818190 := by decide
  rcases family_descends (prefixWord ++ tailWord_818190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818219 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 6]
def baseStart_818219 : Nat := 118140960795 + 818219 * 2 ^ 59
def prefixEnd_818219 : Nat := 4983230072969 + 3 ^ 40 * 818219 * 2
def baseEnd_818219 : Nat := 140046542547079816033195

theorem tailTrace_818219 : CollatzResearch.WordTrace tailWord_818219 prefixEnd_818219 140046542547079816033195 := by
  unfold tailWord_818219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842898622739778524985711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19895265748493185683323807 29842898622739778524985711)
  ·
    refine ⟨44764347934109667787478567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29842898622739778524985711 44764347934109667787478567)
    ·
      refine ⟨67146521901164501681217851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44764347934109667787478567 67146521901164501681217851)
      ·
        refine ⟨100719782851746752521826777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67146521901164501681217851 100719782851746752521826777)
        ·
          refine ⟨75539837138810064391370083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100719782851746752521826777 75539837138810064391370083)
          ·
            refine ⟨113309755708215096587055125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75539837138810064391370083 113309755708215096587055125)
            ·
              refine ⟨5311394798822582652518209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113309755708215096587055125 5311394798822582652518209)
              ·
                refine ⟨3983546099116936989388657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311394798822582652518209 3983546099116936989388657)
                ·
                  refine ⟨2987659574337702742041493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983546099116936989388657 2987659574337702742041493)
                  ·
                    refine ⟨140046542547079816033195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2987659574337702742041493 140046542547079816033195)
                    ·
                      rfl

theorem cell23_818219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_818219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818219 prefixEnd_818219 := by exact prefixLift 818219
  have htrace : WordTrace (prefixWord ++ tailWord_818219) baseStart_818219 baseEnd_818219 := by
    simpa [prefixWord, tailWord_818219, baseEnd_818219] using wordTrace_append hprefix tailTrace_818219
  have hstable : (prefixWord ++ tailWord_818219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818219).length < 2 ^ (prefixWord ++ tailWord_818219).sum := by decide
  have hdescent : baseEnd_818219 < baseStart_818219 := by decide
  rcases family_descends (prefixWord ++ tailWord_818219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818230 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_818230 : Nat := 118140960795 + 818230 * 2 ^ 59
def prefixEnd_818230 : Nat := 4983230072969 + 3 ^ 40 * 818230 * 2
def baseEnd_818230 : Nat := 420145275928438905062035

theorem tailTrace_818230 : CollatzResearch.WordTrace tailWord_818230 prefixEnd_818230 420145275928438905062035 := by
  unfold tailWord_818230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865206239106245462727259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19895533217133284935757429 1865206239106245462727259)
  ·
    refine ⟨2797809358659368194090889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865206239106245462727259 2797809358659368194090889)
    ·
      refine ⟨2098357018994526145568167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797809358659368194090889 2098357018994526145568167)
      ·
        refine ⟨3147535528491789218352251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098357018994526145568167 3147535528491789218352251)
        ·
          refine ⟨4721303292737683827528377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147535528491789218352251 4721303292737683827528377)
          ·
            refine ⟨3540977469553262870646283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4721303292737683827528377 3540977469553262870646283)
            ·
              refine ⟨5311466204329894305969425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540977469553262870646283 5311466204329894305969425)
              ·
                refine ⟨3983599653247420729477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311466204329894305969425 3983599653247420729477069)
                ·
                  refine ⟨1493849869967782773553901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3983599653247420729477069 1493849869967782773553901)
                  ·
                    refine ⟨560193701237918540082713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493849869967782773553901 560193701237918540082713)
                    ·
                      refine ⟨420145275928438905062035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560193701237918540082713 420145275928438905062035)
                      ·
                        rfl

theorem cell23_818230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_818230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818230 prefixEnd_818230 := by exact prefixLift 818230
  have htrace : WordTrace (prefixWord ++ tailWord_818230) baseStart_818230 baseEnd_818230 := by
    simpa [prefixWord, tailWord_818230, baseEnd_818230] using wordTrace_append hprefix tailTrace_818230
  have hstable : (prefixWord ++ tailWord_818230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818230).length < 2 ^ (prefixWord ++ tailWord_818230).sum := by decide
  have hdescent : baseEnd_818230 < baseStart_818230 := by decide
  rcases family_descends (prefixWord ++ tailWord_818230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818236 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_818236 : Nat := 118140960795 + 818236 * 2 ^ 59
def prefixEnd_818236 : Nat := 4983230072969 + 3 ^ 40 * 818236 * 2
def baseEnd_818236 : Nat := 140049452270788627195669

theorem tailTrace_818236 : CollatzResearch.WordTrace tailWord_818236 prefixEnd_818236 140049452270788627195669 := by
  unfold tailWord_818236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921759331839095214177281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19895679109118793618903041 14921759331839095214177281)
  ·
    refine ⟨11191319498879321410632961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14921759331839095214177281 11191319498879321410632961)
    ·
      refine ⟨8393489624159491057974721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11191319498879321410632961 8393489624159491057974721)
      ·
        refine ⟨6295117218119618293481041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8393489624159491057974721 6295117218119618293481041)
        ·
          refine ⟨4721337913589713720110781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6295117218119618293481041 4721337913589713720110781)
          ·
            refine ⟨1770501717596142645041543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4721337913589713720110781 1770501717596142645041543)
            ·
              refine ⟨2655752576394213967562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770501717596142645041543 2655752576394213967562315)
              ·
                refine ⟨3983628864591320951343473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655752576394213967562315 3983628864591320951343473)
                ·
                  refine ⟨2987721648443490713507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983628864591320951343473 2987721648443490713507605)
                  ·
                    refine ⟨140049452270788627195669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2987721648443490713507605 140049452270788627195669)
                    ·
                      rfl

theorem cell23_818236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_818236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818236 prefixEnd_818236 := by exact prefixLift 818236
  have htrace : WordTrace (prefixWord ++ tailWord_818236) baseStart_818236 baseEnd_818236 := by
    simpa [prefixWord, tailWord_818236, baseEnd_818236] using wordTrace_append hprefix tailTrace_818236
  have hstable : (prefixWord ++ tailWord_818236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818236).length < 2 ^ (prefixWord ++ tailWord_818236).sum := by decide
  have hdescent : baseEnd_818236 < baseStart_818236 := by decide
  rcases family_descends (prefixWord ++ tailWord_818236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818243 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 4, 2]
def baseStart_818243 : Nat := 118140960795 + 818243 * 2 ^ 59
def prefixEnd_818243 : Nat := 4983230072969 + 3 ^ 40 * 818243 * 2
def baseEnd_818243 : Nat := 420151951176947354199475

theorem tailTrace_818243 : CollatzResearch.WordTrace tailWord_818243 prefixEnd_818243 420151951176947354199475 := by
  unfold tailWord_818243
  simp only [CollatzResearch.WordTrace]
  refine ⟨29843773974652830623859383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19895849316435220415906255 29843773974652830623859383)
  ·
    refine ⟨44765660961979245935789075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29843773974652830623859383 44765660961979245935789075)
    ·
      refine ⟨67148491442968868903683613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44765660961979245935789075 67148491442968868903683613)
      ·
        refine ⟨25180684291113325838881355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67148491442968868903683613 25180684291113325838881355)
        ·
          refine ⟨37771026436669988758322033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25180684291113325838881355 37771026436669988758322033)
          ·
            refine ⟨28328269827502491568741525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37771026436669988758322033 28328269827502491568741525)
            ·
              refine ⟨1327887648164179292284759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28328269827502491568741525 1327887648164179292284759)
              ·
                refine ⟨1991831472246268938427139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327887648164179292284759 1991831472246268938427139)
                ·
                  refine ⟨2987747208369403407640709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991831472246268938427139 2987747208369403407640709)
                  ·
                    refine ⟨560202601569263138932633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987747208369403407640709 560202601569263138932633)
                    ·
                      refine ⟨420151951176947354199475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560202601569263138932633 420151951176947354199475)
                      ·
                        rfl

theorem cell23_818243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_818243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818243 prefixEnd_818243 := by exact prefixLift 818243
  have htrace : WordTrace (prefixWord ++ tailWord_818243) baseStart_818243 baseEnd_818243 := by
    simpa [prefixWord, tailWord_818243, baseEnd_818243] using wordTrace_append hprefix tailTrace_818243
  have hstable : (prefixWord ++ tailWord_818243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818243).length < 2 ^ (prefixWord ++ tailWord_818243).sum := by decide
  have hdescent : baseEnd_818243 < baseStart_818243 := by decide
  rcases family_descends (prefixWord ++ tailWord_818243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818270 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_818270 : Nat := 118140960795 + 818270 * 2 ^ 59
def prefixEnd_818270 : Nat := 4983230072969 + 3 ^ 40 * 818270 * 2
def baseEnd_818270 : Nat := 140055271718206249520617

theorem tailTrace_818270 : CollatzResearch.WordTrace tailWord_818270 prefixEnd_818270 140055271718206249520617 := by
  unfold tailWord_818270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730594843194376779386533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19896505830370009490061509 3730594843194376779386533)
  ·
    refine ⟨699486533098945646134975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3730594843194376779386533 699486533098945646134975)
    ·
      refine ⟨1049229799648418469202463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699486533098945646134975 1049229799648418469202463)
      ·
        refine ⟨1573844699472627703803695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049229799648418469202463 1573844699472627703803695)
        ·
          refine ⟨2360767049208941555705543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573844699472627703803695 2360767049208941555705543)
          ·
            refine ⟨3541150573813412333558315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360767049208941555705543 3541150573813412333558315)
            ·
              refine ⟨5311725860720118500337473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541150573813412333558315 5311725860720118500337473)
              ·
                refine ⟨3983794395540088875253105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311725860720118500337473 3983794395540088875253105)
                ·
                  refine ⟨2987845796655066656439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983794395540088875253105 2987845796655066656439829)
                  ·
                    refine ⟨140055271718206249520617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2987845796655066656439829 140055271718206249520617)
                    ·
                      rfl

theorem cell23_818270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_818270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818270 prefixEnd_818270 := by exact prefixLift 818270
  have htrace : WordTrace (prefixWord ++ tailWord_818270) baseStart_818270 baseEnd_818270 := by
    simpa [prefixWord, tailWord_818270, baseEnd_818270] using wordTrace_append hprefix tailTrace_818270
  have hstable : (prefixWord ++ tailWord_818270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818270).length < 2 ^ (prefixWord ++ tailWord_818270).sum := by decide
  have hdescent : baseEnd_818270 < baseStart_818270 := by decide
  rcases family_descends (prefixWord ++ tailWord_818270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818294 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_818294 : Nat := 118140960795 + 818294 * 2 ^ 59
def prefixEnd_818294 : Nat := 4983230072969 + 3 ^ 40 * 818294 * 2
def baseEnd_818294 : Nat := 420178138690326654661741

theorem tailTrace_818294 : CollatzResearch.WordTrace tailWord_818294 prefixEnd_818294 420178138690326654661741 := by
  unfold tailWord_818294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865352131091754145872871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19897089398312044222643957 1865352131091754145872871)
  ·
    refine ⟨2798028196637631218809307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865352131091754145872871 2798028196637631218809307)
    ·
      refine ⟨4197042294956446828213961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798028196637631218809307 4197042294956446828213961)
      ·
        refine ⟨3147781721217335121160471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4197042294956446828213961 3147781721217335121160471)
        ·
          refine ⟨4721672581826002681740707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147781721217335121160471 4721672581826002681740707)
          ·
            refine ⟨7082508872739004022611061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721672581826002681740707 7082508872739004022611061)
            ·
              refine ⟨663985206819281627119787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7082508872739004022611061 663985206819281627119787)
              ·
                refine ⟨995977810228922440679681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663985206819281627119787 995977810228922440679681)
                ·
                  refine ⟨746983357671691830509761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995977810228922440679681 746983357671691830509761)
                  ·
                    refine ⟨560237518253768872882321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746983357671691830509761 560237518253768872882321)
                    ·
                      refine ⟨420178138690326654661741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560237518253768872882321 420178138690326654661741)
                      ·
                        rfl

theorem cell23_818294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_818294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818294 prefixEnd_818294 := by exact prefixLift 818294
  have htrace : WordTrace (prefixWord ++ tailWord_818294) baseStart_818294 baseEnd_818294 := by
    simpa [prefixWord, tailWord_818294, baseEnd_818294] using wordTrace_append hprefix tailTrace_818294
  have hstable : (prefixWord ++ tailWord_818294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818294).length < 2 ^ (prefixWord ++ tailWord_818294).sum := by decide
  have hdescent : baseEnd_818294 < baseStart_818294 := by decide
  rcases family_descends (prefixWord ++ tailWord_818294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818316 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_818316 : Nat := 118140960795 + 818316 * 2 ^ 59
def prefixEnd_818316 : Nat := 4983230072969 + 3 ^ 40 * 818316 * 2
def baseEnd_818316 : Nat := 420189435264725568586639

theorem tailTrace_818316 : CollatzResearch.WordTrace tailWord_818316 prefixEnd_818316 420189435264725568586639 := by
  unfold tailWord_818316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14923218251694182045633401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19897624335592242727511201 14923218251694182045633401)
  ·
    refine ⟨11192413688770636534225051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14923218251694182045633401 11192413688770636534225051)
    ·
      refine ⟨16788620533155954801337577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11192413688770636534225051 16788620533155954801337577)
      ·
        refine ⟨12591465399866966101003183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16788620533155954801337577 12591465399866966101003183)
        ·
          refine ⟨18887198099800449151504775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591465399866966101003183 18887198099800449151504775)
          ·
            refine ⟨28330797149700673727257163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887198099800449151504775 28330797149700673727257163)
            ·
              refine ⟨42496195724551010590885745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28330797149700673727257163 42496195724551010590885745)
              ·
                refine ⟨31872146793413257943164309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42496195724551010590885745 31872146793413257943164309)
                ·
                  refine ⟨1494006880941246466085827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31872146793413257943164309 1494006880941246466085827)
                  ·
                    refine ⟨2241010321411869699128741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494006880941246466085827 2241010321411869699128741)
                    ·
                      refine ⟨420189435264725568586639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2241010321411869699128741 420189435264725568586639)
                      ·
                        rfl

theorem cell23_818316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_818316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818316 prefixEnd_818316 := by exact prefixLift 818316
  have htrace : WordTrace (prefixWord ++ tailWord_818316) baseStart_818316 baseEnd_818316 := by
    simpa [prefixWord, tailWord_818316, baseEnd_818316] using wordTrace_append hprefix tailTrace_818316
  have hstable : (prefixWord ++ tailWord_818316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818316).length < 2 ^ (prefixWord ++ tailWord_818316).sum := by decide
  have hdescent : baseEnd_818316 < baseStart_818316 := by decide
  rcases family_descends (prefixWord ++ tailWord_818316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818333 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_818333 : Nat := 118140960795 + 818333 * 2 ^ 59
def prefixEnd_818333 : Nat := 4983230072969 + 3 ^ 40 * 818333 * 2
def baseEnd_818333 : Nat := 420198164435852002074061

theorem tailTrace_818333 : CollatzResearch.WordTrace tailWord_818333 prefixEnd_818333 420198164435852002074061 := by
  unfold tailWord_818333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847056544326775994635653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19898037696217850663090435 29847056544326775994635653)
  ·
    refine ⟨5596323102061270498994185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29847056544326775994635653 5596323102061270498994185)
    ·
      refine ⟨4197242326545952874245639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5596323102061270498994185 4197242326545952874245639)
      ·
        refine ⟨6295863489818929311368459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197242326545952874245639 6295863489818929311368459)
        ·
          refine ⟨9443795234728393967052689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295863489818929311368459 9443795234728393967052689)
          ·
            refine ⟨7082846426046295475289517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9443795234728393967052689 7082846426046295475289517)
            ·
              refine ⟨2656067409767360803233569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7082846426046295475289517 2656067409767360803233569)
              ·
                refine ⟨1992050557325520602425177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656067409767360803233569 1992050557325520602425177)
                ·
                  refine ⟨1494037917994140451818883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992050557325520602425177 1494037917994140451818883)
                  ·
                    refine ⟨2241056876991210677728325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494037917994140451818883 2241056876991210677728325)
                    ·
                      refine ⟨420198164435852002074061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2241056876991210677728325 420198164435852002074061)
                      ·
                        rfl

theorem cell23_818333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_818333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818333 prefixEnd_818333 := by exact prefixLift 818333
  have htrace : WordTrace (prefixWord ++ tailWord_818333) baseStart_818333 baseEnd_818333 := by
    simpa [prefixWord, tailWord_818333, baseEnd_818333] using wordTrace_append hprefix tailTrace_818333
  have hstable : (prefixWord ++ tailWord_818333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818333).length < 2 ^ (prefixWord ++ tailWord_818333).sum := by decide
  have hdescent : baseEnd_818333 < baseStart_818333 := by decide
  rcases family_descends (prefixWord ++ tailWord_818333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818383 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_818383 : Nat := 118140960795 + 818383 * 2 ^ 59
def prefixEnd_818383 : Nat := 4983230072969 + 3 ^ 40 * 818383 * 2
def baseEnd_818383 : Nat := 420223838468576806448831

theorem tailTrace_818383 : CollatzResearch.WordTrace tailWord_818383 prefixEnd_818383 420223838468576806448831 := by
  unfold tailWord_818383
  simp only [CollatzResearch.WordTrace]
  refine ⟨29848880194145634533955803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19899253462763756355970535 29848880194145634533955803)
  ·
    refine ⟨44773320291218451800933705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29848880194145634533955803 44773320291218451800933705)
    ·
      refine ⟨33579990218413838850700279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44773320291218451800933705 33579990218413838850700279)
      ·
        refine ⟨50369985327620758276050419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33579990218413838850700279 50369985327620758276050419)
        ·
          refine ⟨75554977991431137414075629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50369985327620758276050419 75554977991431137414075629)
          ·
            refine ⟨28333116746786676530278361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75554977991431137414075629 28333116746786676530278361)
            ·
              refine ⟨21249837560090007397708771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28333116746786676530278361 21249837560090007397708771)
              ·
                refine ⟨31874756340135011096563157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21249837560090007397708771 31874756340135011096563157)
                ·
                  refine ⟨747064601721914322575699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31874756340135011096563157 747064601721914322575699)
                  ·
                    refine ⟨1120596902582871483863549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747064601721914322575699 1120596902582871483863549)
                    ·
                      refine ⟨420223838468576806448831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120596902582871483863549 420223838468576806448831)
                      ·
                        rfl

theorem cell23_818383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_818383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818383 prefixEnd_818383 := by exact prefixLift 818383
  have htrace : WordTrace (prefixWord ++ tailWord_818383) baseStart_818383 baseEnd_818383 := by
    simpa [prefixWord, tailWord_818383, baseEnd_818383] using wordTrace_append hprefix tailTrace_818383
  have hstable : (prefixWord ++ tailWord_818383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818383).length < 2 ^ (prefixWord ++ tailWord_818383).sum := by decide
  have hdescent : baseEnd_818383 < baseStart_818383 := by decide
  rcases family_descends (prefixWord ++ tailWord_818383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818393 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 5, 2]
def baseStart_818393 : Nat := 118140960795 + 818393 * 2 ^ 59
def prefixEnd_818393 : Nat := 4983230072969 + 3 ^ 40 * 818393 * 2
def baseEnd_818393 : Nat := 420228973275121767323785

theorem tailTrace_818393 : CollatzResearch.WordTrace tailWord_818393 prefixEnd_818393 420228973275121767323785 := by
  unfold tailWord_818393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849244924109406241819833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19899496616072937494546555 29849244924109406241819833)
  ·
    refine ⟨22386933693082054681364875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29849244924109406241819833 22386933693082054681364875)
    ·
      refine ⟨33580400539623082022047313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22386933693082054681364875 33580400539623082022047313)
      ·
        refine ⟨25185300404717311516535485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33580400539623082022047313 25185300404717311516535485)
        ·
          refine ⟨9444487651768991818700807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25185300404717311516535485 9444487651768991818700807)
          ·
            refine ⟨14166731477653487728051211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444487651768991818700807 14166731477653487728051211)
            ·
              refine ⟨21250097216480231592076817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166731477653487728051211 21250097216480231592076817)
              ·
                refine ⟨15937572912360173694057613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21250097216480231592076817 15937572912360173694057613)
                ·
                  refine ⟨5976589842135065135271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15937572912360173694057613 5976589842135065135271605)
                  ·
                    refine ⟨560305297700162356431713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5976589842135065135271605 560305297700162356431713)
                    ·
                      refine ⟨420228973275121767323785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560305297700162356431713 420228973275121767323785)
                      ·
                        rfl

theorem cell23_818393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_818393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818393 prefixEnd_818393 := by exact prefixLift 818393
  have htrace : WordTrace (prefixWord ++ tailWord_818393) baseStart_818393 baseEnd_818393 := by
    simpa [prefixWord, tailWord_818393, baseEnd_818393] using wordTrace_append hprefix tailTrace_818393
  have hstable : (prefixWord ++ tailWord_818393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818393).length < 2 ^ (prefixWord ++ tailWord_818393).sum := by decide
  have hdescent : baseEnd_818393 < baseStart_818393 := by decide
  rcases family_descends (prefixWord ++ tailWord_818393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818423 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_818423 : Nat := 118140960795 + 818423 * 2 ^ 59
def prefixEnd_818423 : Nat := 4983230072969 + 3 ^ 40 * 818423 * 2
def baseEnd_818423 : Nat := 420244377694756649948647

theorem tailTrace_818423 : CollatzResearch.WordTrace tailWord_818423 prefixEnd_818423 420244377694756649948647 := by
  unfold tailWord_818423
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850339114000721365411923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19900226076000480910274615 29850339114000721365411923)
  ·
    refine ⟨44775508671001082048117885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850339114000721365411923 44775508671001082048117885)
    ·
      refine ⟨16790815751625405768044207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44775508671001082048117885 16790815751625405768044207)
      ·
        refine ⟨25186223627438108652066311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16790815751625405768044207 25186223627438108652066311)
        ·
          refine ⟨37779335441157162978099467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25186223627438108652066311 37779335441157162978099467)
          ·
            refine ⟨56669003161735744467149201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37779335441157162978099467 56669003161735744467149201)
            ·
              refine ⟨42501752371301808350361901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56669003161735744467149201 42501752371301808350361901)
              ·
                refine ⟨15938157139238178131385713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42501752371301808350361901 15938157139238178131385713)
                ·
                  refine ⟨11953617854428633598539285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15938157139238178131385713 11953617854428633598539285)
                  ·
                    refine ⟨560325836926342199931529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11953617854428633598539285 560325836926342199931529)
                    ·
                      refine ⟨420244377694756649948647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560325836926342199931529 420244377694756649948647)
                      ·
                        rfl

theorem cell23_818423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_818423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818423 prefixEnd_818423 := by exact prefixLift 818423
  have htrace : WordTrace (prefixWord ++ tailWord_818423) baseStart_818423 baseEnd_818423 := by
    simpa [prefixWord, tailWord_818423, baseEnd_818423] using wordTrace_append hprefix tailTrace_818423
  have hstable : (prefixWord ++ tailWord_818423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818423).length < 2 ^ (prefixWord ++ tailWord_818423).sum := by decide
  have hdescent : baseEnd_818423 < baseStart_818423 := by decide
  rcases family_descends (prefixWord ++ tailWord_818423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818433 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_818433 : Nat := 118140960795 + 818433 * 2 ^ 59
def prefixEnd_818433 : Nat := 4983230072969 + 3 ^ 40 * 818433 * 2
def baseEnd_818433 : Nat := 140083170833767203607867

theorem tailTrace_818433 : CollatzResearch.WordTrace tailWord_818433 prefixEnd_818433 140083170833767203607867 := by
  unfold tailWord_818433
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850703843964493073275953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19900469229309662048850635 29850703843964493073275953)
  ·
    refine ⟨22388027882973369804956965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29850703843964493073275953 22388027882973369804956965)
    ·
      refine ⟨4197755228057506838429431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22388027882973369804956965 4197755228057506838429431)
      ·
        refine ⟨6296632842086260257644147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197755228057506838429431 6296632842086260257644147)
        ·
          refine ⟨9444949263129390386466221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296632842086260257644147 9444949263129390386466221)
          ·
            refine ⟨3541855973673521394924833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9444949263129390386466221 3541855973673521394924833)
            ·
              refine ⟨2656391980255141046193625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541855973673521394924833 2656391980255141046193625)
              ·
                refine ⟨1992293985191355784645219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656391980255141046193625 1992293985191355784645219)
                ·
                  refine ⟨2988440977787033676967829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992293985191355784645219 2988440977787033676967829)
                  ·
                    refine ⟨140083170833767203607867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2988440977787033676967829 140083170833767203607867)
                    ·
                      rfl

theorem cell23_818433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_818433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818433 prefixEnd_818433 := by exact prefixLift 818433
  have htrace : WordTrace (prefixWord ++ tailWord_818433) baseStart_818433 baseEnd_818433 := by
    simpa [prefixWord, tailWord_818433, baseEnd_818433] using wordTrace_append hprefix tailTrace_818433
  have hstable : (prefixWord ++ tailWord_818433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818433).length < 2 ^ (prefixWord ++ tailWord_818433).sum := by decide
  have hdescent : baseEnd_818433 < baseStart_818433 := by decide
  rcases family_descends (prefixWord ++ tailWord_818433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818467 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 2, 4]
def baseStart_818467 : Nat := 118140960795 + 818467 * 2 ^ 59
def prefixEnd_818467 : Nat := 4983230072969 + 3 ^ 40 * 818467 * 2
def baseEnd_818467 : Nat := 140088990281184825932815

theorem tailTrace_818467 : CollatzResearch.WordTrace tailWord_818467 prefixEnd_818467 140088990281184825932815 := by
  unfold tailWord_818467
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851943925841316880013655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19901295950560877920009103 29851943925841316880013655)
  ·
    refine ⟨44777915888761975320020483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29851943925841316880013655 44777915888761975320020483)
    ·
      refine ⟨67166873833142962980030725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44777915888761975320020483 67166873833142962980030725)
      ·
        refine ⟨12593788843714305558755761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67166873833142962980030725 12593788843714305558755761)
        ·
          refine ⟨9445341632785729169066821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593788843714305558755761 9445341632785729169066821)
          ·
            refine ⟨1771001556147324219200029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9445341632785729169066821 1771001556147324219200029)
            ·
              refine ⟨664125583555246582200011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1771001556147324219200029 664125583555246582200011)
              ·
                refine ⟨996188375332869873300017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664125583555246582200011 996188375332869873300017)
                ·
                  refine ⟨747141281499652404975013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996188375332869873300017 747141281499652404975013)
                  ·
                    refine ⟨140088990281184825932815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 747141281499652404975013 140088990281184825932815)
                    ·
                      rfl

theorem cell23_818467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 4].length) (baseStart_818467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818467 prefixEnd_818467 := by exact prefixLift 818467
  have htrace : WordTrace (prefixWord ++ tailWord_818467) baseStart_818467 baseEnd_818467 := by
    simpa [prefixWord, tailWord_818467, baseEnd_818467] using wordTrace_append hprefix tailTrace_818467
  have hstable : (prefixWord ++ tailWord_818467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818467).length < 2 ^ (prefixWord ++ tailWord_818467).sum := by decide
  have hdescent : baseEnd_818467 < baseStart_818467 := by decide
  rcases family_descends (prefixWord ++ tailWord_818467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818474 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_818474 : Nat := 118140960795 + 818474 * 2 ^ 59
def prefixEnd_818474 : Nat := 4983230072969 + 3 ^ 40 * 818474 * 2
def baseEnd_818474 : Nat := 420270565208135950410913

theorem tailTrace_818474 : CollatzResearch.WordTrace tailWord_818474 prefixEnd_818474 420270565208135950410913 := by
  unfold tailWord_818474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463049809203989268879619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19901466157877304717012317 7463049809203989268879619)
  ·
    refine ⟨11194574713805983903319429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463049809203989268879619 11194574713805983903319429)
    ·
      refine ⟨2098982758838621981872393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11194574713805983903319429 2098982758838621981872393)
      ·
        refine ⟨1574237069128966486404295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098982758838621981872393 1574237069128966486404295)
        ·
          refine ⟨2361355603693449729606443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574237069128966486404295 2361355603693449729606443)
          ·
            refine ⟨3542033405540174594409665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361355603693449729606443 3542033405540174594409665)
            ·
              refine ⟨2656525054155130945807249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542033405540174594409665 2656525054155130945807249)
              ·
                refine ⟨1992393790616348209355437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656525054155130945807249 1992393790616348209355437)
                ·
                  refine ⟨747147671481130578508289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1992393790616348209355437 747147671481130578508289)
                  ·
                    refine ⟨560360753610847933881217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747147671481130578508289 560360753610847933881217)
                    ·
                      refine ⟨420270565208135950410913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560360753610847933881217 420270565208135950410913)
                      ·
                        rfl

theorem cell23_818474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_818474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818474 prefixEnd_818474 := by exact prefixLift 818474
  have htrace : WordTrace (prefixWord ++ tailWord_818474) baseStart_818474 baseEnd_818474 := by
    simpa [prefixWord, tailWord_818474, baseEnd_818474] using wordTrace_append hprefix tailTrace_818474
  have hstable : (prefixWord ++ tailWord_818474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818474).length < 2 ^ (prefixWord ++ tailWord_818474).sum := by decide
  have hdescent : baseEnd_818474 < baseStart_818474 := by decide
  rcases family_descends (prefixWord ++ tailWord_818474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818490 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_818490 : Nat := 118140960795 + 818490 * 2 ^ 59
def prefixEnd_818490 : Nat := 4983230072969 + 3 ^ 40 * 818490 * 2
def baseEnd_818490 : Nat := 420278780898607887810839

theorem tailTrace_818490 : CollatzResearch.WordTrace tailWord_818490 prefixEnd_818490 420278780898607887810839 := by
  unfold tailWord_818490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463195701189497952025231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19901855203171994538733949 7463195701189497952025231)
  ·
    refine ⟨11194793551784246928037847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463195701189497952025231 11194793551784246928037847)
    ·
      refine ⟨16792190327676370392056771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194793551784246928037847 16792190327676370392056771)
      ·
        refine ⟨25188285491514555588085157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792190327676370392056771 25188285491514555588085157)
        ·
          refine ⟨4722803529658979172765967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25188285491514555588085157 4722803529658979172765967)
          ·
            refine ⟨7084205294488468759148951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722803529658979172765967 7084205294488468759148951)
            ·
              refine ⟨10626307941732703138723427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084205294488468759148951 10626307941732703138723427)
              ·
                refine ⟨15939461912599054708085141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626307941732703138723427 15939461912599054708085141)
                ·
                  refine ⟨747162277153080689441491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15939461912599054708085141 747162277153080689441491)
                  ·
                    refine ⟨1120743415729621034162237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747162277153080689441491 1120743415729621034162237)
                    ·
                      refine ⟨420278780898607887810839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120743415729621034162237 420278780898607887810839)
                      ·
                        rfl

theorem cell23_818490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_818490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818490 prefixEnd_818490 := by exact prefixLift 818490
  have htrace : WordTrace (prefixWord ++ tailWord_818490) baseStart_818490 baseEnd_818490 := by
    simpa [prefixWord, tailWord_818490, baseEnd_818490] using wordTrace_append hprefix tailTrace_818490
  have hstable : (prefixWord ++ tailWord_818490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818490).length < 2 ^ (prefixWord ++ tailWord_818490).sum := by decide
  have hdescent : baseEnd_818490 < baseStart_818490 := by decide
  rcases family_descends (prefixWord ++ tailWord_818490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818513 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_818513 : Nat := 118140960795 + 818513 * 2 ^ 59
def prefixEnd_818513 : Nat := 4983230072969 + 3 ^ 40 * 818513 * 2
def baseEnd_818513 : Nat := 420290590953661297823233

theorem tailTrace_818513 : CollatzResearch.WordTrace tailWord_818513 prefixEnd_818513 420290590953661297823233 := by
  unfold tailWord_818513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853621683674666736188193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19902414455783111157458795 29853621683674666736188193)
  ·
    refine ⟨22390216262756000052141145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29853621683674666736188193 22390216262756000052141145)
    ·
      refine ⟨16792662197067000039105859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22390216262756000052141145 16792662197067000039105859)
      ·
        refine ⟨25188993295600500058658789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792662197067000039105859 25188993295600500058658789)
        ·
          refine ⟨4722936242925093760998523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25188993295600500058658789 4722936242925093760998523)
          ·
            refine ⟨7084404364387640641497785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722936242925093760998523 7084404364387640641497785)
            ·
              refine ⟨5313303273290730481123339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7084404364387640641497785 5313303273290730481123339)
              ·
                refine ⟨7969954909936095721685009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313303273290730481123339 7969954909936095721685009)
                ·
                  refine ⟨5977466182452071791263757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969954909936095721685009 5977466182452071791263757)
                  ·
                    refine ⟨2241549818419526921723909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5977466182452071791263757 2241549818419526921723909)
                    ·
                      refine ⟨420290590953661297823233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2241549818419526921723909 420290590953661297823233)
                      ·
                        rfl

theorem cell23_818513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_818513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818513 prefixEnd_818513 := by exact prefixLift 818513
  have htrace : WordTrace (prefixWord ++ tailWord_818513) baseStart_818513 baseEnd_818513 := by
    simpa [prefixWord, tailWord_818513, baseEnd_818513] using wordTrace_append hprefix tailTrace_818513
  have hstable : (prefixWord ++ tailWord_818513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818513).length < 2 ^ (prefixWord ++ tailWord_818513).sum := by decide
  have hdescent : baseEnd_818513 < baseStart_818513 := by decide
  rcases family_descends (prefixWord ++ tailWord_818513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818518 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_818518 : Nat := 118140960795 + 818518 * 2 ^ 59
def prefixEnd_818518 : Nat := 4983230072969 + 3 ^ 40 * 818518 * 2
def baseEnd_818518 : Nat := 140097719452311259420237

theorem tailTrace_818518 : CollatzResearch.WordTrace tailWord_818518 prefixEnd_818518 140097719452311259420237 := by
  unfold tailWord_818518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865862753041034536882513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19902536032437701726746805 1865862753041034536882513)
  ·
    refine ⟨1399397064780775902661885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865862753041034536882513 1399397064780775902661885)
    ·
      refine ⟨524773899292790963498207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1399397064780775902661885 524773899292790963498207)
      ·
        refine ⟨787160848939186445247311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524773899292790963498207 787160848939186445247311)
        ·
          refine ⟨1180741273408779667870967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787160848939186445247311 1180741273408779667870967)
          ·
            refine ⟨1771111910113169501806451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180741273408779667870967 1771111910113169501806451)
            ·
              refine ⟨2656667865169754252709677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771111910113169501806451 2656667865169754252709677)
              ·
                refine ⟨996250449438657844766129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2656667865169754252709677 996250449438657844766129)
                ·
                  refine ⟨747187837078993383574597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996250449438657844766129 747187837078993383574597)
                  ·
                    refine ⟨140097719452311259420237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 747187837078993383574597 140097719452311259420237)
                    ·
                      rfl

theorem cell23_818518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_818518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818518 prefixEnd_818518 := by exact prefixLift 818518
  have htrace : WordTrace (prefixWord ++ tailWord_818518) baseStart_818518 baseEnd_818518 := by
    simpa [prefixWord, tailWord_818518, baseEnd_818518] using wordTrace_append hprefix tailTrace_818518
  have hstable : (prefixWord ++ tailWord_818518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818518).length < 2 ^ (prefixWord ++ tailWord_818518).sum := by decide
  have hdescent : baseEnd_818518 < baseStart_818518 := by decide
  rcases family_descends (prefixWord ++ tailWord_818518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818533 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_818533 : Nat := 118140960795 + 818533 * 2 ^ 59
def prefixEnd_818533 : Nat := 4983230072969 + 3 ^ 40 * 818533 * 2
def baseEnd_818533 : Nat := 420300860566751219573141

theorem tailTrace_818533 : CollatzResearch.WordTrace tailWord_818533 prefixEnd_818533 420300860566751219573141 := by
  unfold tailWord_818533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29854351143602210151916253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19902900762401473434610835 29854351143602210151916253)
  ·
    refine ⟨11195381678850828806968595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29854351143602210151916253 11195381678850828806968595)
    ·
      refine ⟨16793072518276243210452893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195381678850828806968595 16793072518276243210452893)
      ·
        refine ⟨6297402194353591203919835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16793072518276243210452893 6297402194353591203919835)
        ·
          refine ⟨9446103291530386805879753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297402194353591203919835 9446103291530386805879753)
          ·
            refine ⟨7084577468647790104409815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9446103291530386805879753 7084577468647790104409815)
            ·
              refine ⟨10626866202971685156614723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084577468647790104409815 10626866202971685156614723)
              ·
                refine ⟨15940299304457527734922085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626866202971685156614723 15940299304457527734922085)
                ·
                  refine ⟨2988806119585786450297891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15940299304457527734922085 2988806119585786450297891)
                  ·
                    refine ⟨4483209179378679675446837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988806119585786450297891 4483209179378679675446837)
                    ·
                      refine ⟨420300860566751219573141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4483209179378679675446837 420300860566751219573141)
                      ·
                        rfl

theorem cell23_818533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_818533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818533 prefixEnd_818533 := by exact prefixLift 818533
  have htrace : WordTrace (prefixWord ++ tailWord_818533) baseStart_818533 baseEnd_818533 := by
    simpa [prefixWord, tailWord_818533, baseEnd_818533] using wordTrace_append hprefix tailTrace_818533
  have hstable : (prefixWord ++ tailWord_818533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818533).length < 2 ^ (prefixWord ++ tailWord_818533).sum := by decide
  have hdescent : baseEnd_818533 < baseStart_818533 := by decide
  rcases family_descends (prefixWord ++ tailWord_818533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818558 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_818558 : Nat := 118140960795 + 818558 * 2 ^ 59
def prefixEnd_818558 : Nat := 4983230072969 + 3 ^ 40 * 818558 * 2
def baseEnd_818558 : Nat := 420313697583113621760527

theorem tailTrace_818558 : CollatzResearch.WordTrace tailWord_818558 prefixEnd_818558 420313697583113621760527 := by
  unfold tailWord_818558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731907871063954927697041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19903508645674426281050885 3731907871063954927697041)
  ·
    refine ⟨2798930903297966195772781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731907871063954927697041 2798930903297966195772781)
    ·
      refine ⟨1049599088736737323414793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2798930903297966195772781 1049599088736737323414793)
      ·
        refine ⟨787199316552552992561095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049599088736737323414793 787199316552552992561095)
        ·
          refine ⟨1180798974828829488841643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787199316552552992561095 1180798974828829488841643)
          ·
            refine ⟨1771198462243244233262465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180798974828829488841643 1771198462243244233262465)
            ·
              refine ⟨1328398846682433174946849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771198462243244233262465 1328398846682433174946849)
              ·
                refine ⟨996299135011824881210137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328398846682433174946849 996299135011824881210137)
                ·
                  refine ⟨747224351258868660907603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996299135011824881210137 747224351258868660907603)
                  ·
                    refine ⟨1120836526888302991361405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747224351258868660907603 1120836526888302991361405)
                    ·
                      refine ⟨420313697583113621760527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120836526888302991361405 420313697583113621760527)
                      ·
                        rfl

theorem cell23_818558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_818558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818558 prefixEnd_818558 := by exact prefixLift 818558
  have htrace : WordTrace (prefixWord ++ tailWord_818558) baseStart_818558 baseEnd_818558 := by
    simpa [prefixWord, tailWord_818558, baseEnd_818558] using wordTrace_append hprefix tailTrace_818558
  have hstable : (prefixWord ++ tailWord_818558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818558).length < 2 ^ (prefixWord ++ tailWord_818558).sum := by decide
  have hdescent : baseEnd_818558 < baseStart_818558 := by decide
  rcases family_descends (prefixWord ++ tailWord_818558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818564 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_818564 : Nat := 118140960795 + 818564 * 2 ^ 59
def prefixEnd_818564 : Nat := 4983230072969 + 3 ^ 40 * 818564 * 2
def baseEnd_818564 : Nat := 420316778467040598285499

theorem tailTrace_818564 : CollatzResearch.WordTrace tailWord_818564 prefixEnd_818564 420316778467040598285499 := by
  unfold tailWord_818564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927740903244951223147373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19903654537659934964196497 14927740903244951223147373)
  ·
    refine ⟨5597902838716856708680265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14927740903244951223147373 5597902838716856708680265)
    ·
      refine ⟨4198427129037642531510199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597902838716856708680265 4198427129037642531510199)
      ·
        refine ⟨6297640693556463797265299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198427129037642531510199 6297640693556463797265299)
        ·
          refine ⟨9446461040334695695897949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297640693556463797265299 9446461040334695695897949)
          ·
            refine ⟨3542422890125510885961731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9446461040334695695897949 3542422890125510885961731)
            ·
              refine ⟨5313634335188266328942597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542422890125510885961731 5313634335188266328942597)
              ·
                refine ⟨996306437847799936676737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313634335188266328942597 996306437847799936676737)
                ·
                  refine ⟨747229828385849952507553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996306437847799936676737 747229828385849952507553)
                  ·
                    refine ⟨560422371289387464380665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747229828385849952507553 560422371289387464380665)
                    ·
                      refine ⟨420316778467040598285499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560422371289387464380665 420316778467040598285499)
                      ·
                        rfl

theorem cell23_818564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_818564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818564 prefixEnd_818564 := by exact prefixLift 818564
  have htrace : WordTrace (prefixWord ++ tailWord_818564) baseStart_818564 baseEnd_818564 := by
    simpa [prefixWord, tailWord_818564, baseEnd_818564] using wordTrace_append hprefix tailTrace_818564
  have hstable : (prefixWord ++ tailWord_818564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818564).length < 2 ^ (prefixWord ++ tailWord_818564).sum := by decide
  have hdescent : baseEnd_818564 < baseStart_818564 := by decide
  rcases family_descends (prefixWord ++ tailWord_818564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818583 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 7]
def baseStart_818583 : Nat := 118140960795 + 818583 * 2 ^ 59
def prefixEnd_818583 : Nat := 4983230072969 + 3 ^ 40 * 818583 * 2
def baseEnd_818583 : Nat := 140108844866492007982637

theorem tailTrace_818583 : CollatzResearch.WordTrace tailWord_818583 prefixEnd_818583 140108844866492007982637 := by
  unfold tailWord_818583
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856174793421068691236403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19904116528947379127490935 29856174793421068691236403)
  ·
    refine ⟨44784262190131603036854605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29856174793421068691236403 44784262190131603036854605)
    ·
      refine ⟨16794098321299351138820477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44784262190131603036854605 16794098321299351138820477)
      ·
        refine ⟨6297786870487256677057679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16794098321299351138820477 6297786870487256677057679)
        ·
          refine ⟨9446680305730885015586519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297786870487256677057679 9446680305730885015586519)
          ·
            refine ⟨14170020458596327523379779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446680305730885015586519 14170020458596327523379779)
            ·
              refine ⟨21255030687894491285069669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14170020458596327523379779 21255030687894491285069669)
              ·
                refine ⟨3985318253980217115950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21255030687894491285069669 3985318253980217115950563)
                ·
                  refine ⟨5977977380970325673925845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985318253980217115950563 5977977380970325673925845)
                  ·
                    refine ⟨140108844866492007982637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5977977380970325673925845 140108844866492007982637)
                    ·
                      rfl

theorem cell23_818583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_818583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818583 prefixEnd_818583 := by exact prefixLift 818583
  have htrace : WordTrace (prefixWord ++ tailWord_818583) baseStart_818583 baseEnd_818583 := by
    simpa [prefixWord, tailWord_818583, baseEnd_818583] using wordTrace_append hprefix tailTrace_818583
  have hstable : (prefixWord ++ tailWord_818583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818583).length < 2 ^ (prefixWord ++ tailWord_818583).sum := by decide
  have hdescent : baseEnd_818583 < baseStart_818583 := by decide
  rcases family_descends (prefixWord ++ tailWord_818583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818623 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_818623 : Nat := 118140960795 + 818623 * 2 ^ 59
def prefixEnd_818623 : Nat := 4983230072969 + 3 ^ 40 * 818623 * 2
def baseEnd_818623 : Nat := 420347073825655867447727

theorem tailTrace_818623 : CollatzResearch.WordTrace tailWord_818623 prefixEnd_818623 420347073825655867447727 := by
  unfold tailWord_818623
  simp only [CollatzResearch.WordTrace]
  refine ⟨29857633713276155522692523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19905089142184103681795015 29857633713276155522692523)
  ·
    refine ⟨44786450569914233284038785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29857633713276155522692523 44786450569914233284038785)
    ·
      refine ⟨33589837927435674963029089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44786450569914233284038785 33589837927435674963029089)
      ·
        refine ⟨25192378445576756222271817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33589837927435674963029089 25192378445576756222271817)
        ·
          refine ⟨18894283834182567166703863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25192378445576756222271817 18894283834182567166703863)
          ·
            refine ⟨28341425751273850750055795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894283834182567166703863 28341425751273850750055795)
            ·
              refine ⟨42512138626910776125083693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28341425751273850750055795 42512138626910776125083693)
              ·
                refine ⟨15942051985091541046906385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42512138626910776125083693 15942051985091541046906385)
                ·
                  refine ⟨11956538988818655785179789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15942051985091541046906385 11956538988818655785179789)
                  ·
                    refine ⟨4483702120806995919442421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11956538988818655785179789 4483702120806995919442421)
                    ·
                      refine ⟨420347073825655867447727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4483702120806995919442421 420347073825655867447727)
                      ·
                        rfl

theorem cell23_818623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_818623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818623 prefixEnd_818623 := by exact prefixLift 818623
  have htrace : WordTrace (prefixWord ++ tailWord_818623) baseStart_818623 baseEnd_818623 := by
    simpa [prefixWord, tailWord_818623, baseEnd_818623] using wordTrace_append hprefix tailTrace_818623
  have hstable : (prefixWord ++ tailWord_818623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818623).length < 2 ^ (prefixWord ++ tailWord_818623).sum := by decide
  have hdescent : baseEnd_818623 < baseStart_818623 := by decide
  rcases family_descends (prefixWord ++ tailWord_818623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818633 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_818633 : Nat := 118140960795 + 818633 * 2 ^ 59
def prefixEnd_818633 : Nat := 4983230072969 + 3 ^ 40 * 818633 * 2
def baseEnd_818633 : Nat := 420352208632200828322681

theorem tailTrace_818633 : CollatzResearch.WordTrace tailWord_818633 prefixEnd_818633 420352208632200828322681 := by
  unfold tailWord_818633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29857998443239927230556553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19905332295493284820371035 29857998443239927230556553)
  ·
    refine ⟨22393498832429945422917415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29857998443239927230556553 22393498832429945422917415)
    ·
      refine ⟨33590248248644918134376123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22393498832429945422917415 33590248248644918134376123)
      ·
        refine ⟨50385372372967377201564185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33590248248644918134376123 50385372372967377201564185)
        ·
          refine ⟨37789029279725532901173139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50385372372967377201564185 37789029279725532901173139)
          ·
            refine ⟨56683543919588299351759709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37789029279725532901173139 56683543919588299351759709)
            ·
              refine ⟨21256328969845612256909891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56683543919588299351759709 21256328969845612256909891)
              ·
                refine ⟨31884493454768418385364837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21256328969845612256909891 31884493454768418385364837)
                ·
                  refine ⟨5978342522769078447255907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31884493454768418385364837 5978342522769078447255907)
                  ·
                    refine ⟨8967513784153617670883861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978342522769078447255907 8967513784153617670883861)
                    ·
                      refine ⟨420352208632200828322681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8967513784153617670883861 420352208632200828322681)
                      ·
                        rfl

theorem cell23_818633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_818633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818633 prefixEnd_818633 := by exact prefixLift 818633
  have htrace : WordTrace (prefixWord ++ tailWord_818633) baseStart_818633 baseEnd_818633 := by
    simpa [prefixWord, tailWord_818633, baseEnd_818633] using wordTrace_append hprefix tailTrace_818633
  have hstable : (prefixWord ++ tailWord_818633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818633).length < 2 ^ (prefixWord ++ tailWord_818633).sum := by decide
  have hdescent : baseEnd_818633 < baseStart_818633 := by decide
  rcases family_descends (prefixWord ++ tailWord_818633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818640 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_818640 : Nat := 118140960795 + 818640 * 2 ^ 59
def prefixEnd_818640 : Nat := 4983230072969 + 3 ^ 40 * 818640 * 2
def baseEnd_818640 : Nat := 420355802996782300935149

theorem tailTrace_818640 : CollatzResearch.WordTrace tailWord_818640 prefixEnd_818640 420355802996782300935149 := by
  unfold tailWord_818640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929126877107283713030687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19905502502809711617374249 14929126877107283713030687)
  ·
    refine ⟨22393690315660925569546031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14929126877107283713030687 22393690315660925569546031)
    ·
      refine ⟨33590535473491388354319047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22393690315660925569546031 33590535473491388354319047)
      ·
        refine ⟨50385803210237082531478571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33590535473491388354319047 50385803210237082531478571)
        ·
          refine ⟨75578704815355623797217857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50385803210237082531478571 75578704815355623797217857)
          ·
            refine ⟨56684028611516717847913393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75578704815355623797217857 56684028611516717847913393)
            ·
              refine ⟨42513021458637538385935045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56684028611516717847913393 42513021458637538385935045)
              ·
                refine ⟨7971191523494538447362821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42513021458637538385935045 7971191523494538447362821)
                ·
                  refine ⟨1494598410655225958880529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7971191523494538447362821 1494598410655225958880529)
                  ·
                    refine ⟨1120948807991419469160397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1494598410655225958880529 1120948807991419469160397)
                    ·
                      refine ⟨420355802996782300935149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120948807991419469160397 420355802996782300935149)
                      ·
                        rfl

theorem cell23_818640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_818640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818640 prefixEnd_818640 := by exact prefixLift 818640
  have htrace : WordTrace (prefixWord ++ tailWord_818640) baseStart_818640 baseEnd_818640 := by
    simpa [prefixWord, tailWord_818640, baseEnd_818640] using wordTrace_append hprefix tailTrace_818640
  have hstable : (prefixWord ++ tailWord_818640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818640).length < 2 ^ (prefixWord ++ tailWord_818640).sum := by decide
  have hdescent : baseEnd_818640 < baseStart_818640 := by decide
  rcases family_descends (prefixWord ++ tailWord_818640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818674 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_818674 : Nat := 118140960795 + 818674 * 2 ^ 59
def prefixEnd_818674 : Nat := 4983230072969 + 3 ^ 40 * 818674 * 2
def baseEnd_818674 : Nat := 420373261339035167909993

theorem tailTrace_818674 : CollatzResearch.WordTrace tailWord_818674 prefixEnd_818674 420373261339035167909993 := by
  unfold tailWord_818674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464873459022847808199769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19906329224060927488532717 7464873459022847808199769)
  ·
    refine ⟨5598655094267135856149827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7464873459022847808199769 5598655094267135856149827)
    ·
      refine ⟨8397982641400703784224741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598655094267135856149827 8397982641400703784224741)
      ·
        refine ⟨1574621745262631959542139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8397982641400703784224741 1574621745262631959542139)
        ·
          refine ⟨2361932617893947939313209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574621745262631959542139 2361932617893947939313209)
          ·
            refine ⟨1771449463420460954484907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361932617893947939313209 1771449463420460954484907)
            ·
              refine ⟨2657174195130691431727361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771449463420460954484907 2657174195130691431727361)
              ·
                refine ⟨1992880646348018573795521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657174195130691431727361 1992880646348018573795521)
                ·
                  refine ⟨1494660484761013930346641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992880646348018573795521 1494660484761013930346641)
                  ·
                    refine ⟨1120995363570760447759981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1494660484761013930346641 1120995363570760447759981)
                    ·
                      refine ⟨420373261339035167909993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1120995363570760447759981 420373261339035167909993)
                      ·
                        rfl

theorem cell23_818674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_818674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818674 prefixEnd_818674 := by exact prefixLift 818674
  have htrace : WordTrace (prefixWord ++ tailWord_818674) baseStart_818674 baseEnd_818674 := by
    simpa [prefixWord, tailWord_818674, baseEnd_818674] using wordTrace_append hprefix tailTrace_818674
  have hstable : (prefixWord ++ tailWord_818674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818674).length < 2 ^ (prefixWord ++ tailWord_818674).sum := by decide
  have hdescent : baseEnd_818674 < baseStart_818674 := by decide
  rcases family_descends (prefixWord ++ tailWord_818674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818677 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 8]
def baseStart_818677 : Nat := 118140960795 + 818677 * 2 ^ 59
def prefixEnd_818677 : Nat := 4983230072969 + 3 ^ 40 * 818677 * 2
def baseEnd_818677 : Nat := 46708311308999850685831

theorem tailTrace_818677 : CollatzResearch.WordTrace tailWord_818677 prefixEnd_818677 46708311308999850685831 := by
  unfold tailWord_818677
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859603255080522745158285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906402170053681830105523 29859603255080522745158285)
  ·
    refine ⟨11197351220655196029434357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29859603255080522745158285 11197351220655196029434357)
    ·
      refine ⟨1049751676936424627759471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11197351220655196029434357 1049751676936424627759471)
      ·
        refine ⟨1574627515404636941639207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049751676936424627759471 1574627515404636941639207)
        ·
          refine ⟨2361941273106955412458811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574627515404636941639207 2361941273106955412458811)
          ·
            refine ⟨3542911909660433118688217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361941273106955412458811 3542911909660433118688217)
            ·
              refine ⟨2657183932245324839016163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542911909660433118688217 2657183932245324839016163)
              ·
                refine ⟨3985775898367987258524245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657183932245324839016163 3985775898367987258524245)
                ·
                  refine ⟨46708311308999850685831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3985775898367987258524245 46708311308999850685831)
                  ·
                    rfl

theorem cell23_818677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_818677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818677 prefixEnd_818677 := by exact prefixLift 818677
  have htrace : WordTrace (prefixWord ++ tailWord_818677) baseStart_818677 baseEnd_818677 := by
    simpa [prefixWord, tailWord_818677, baseEnd_818677] using wordTrace_append hprefix tailTrace_818677
  have hstable : (prefixWord ++ tailWord_818677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818677).length < 2 ^ (prefixWord ++ tailWord_818677).sum := by decide
  have hdescent : baseEnd_818677 < baseStart_818677 := by decide
  rcases family_descends (prefixWord ++ tailWord_818677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818687 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_818687 : Nat := 118140960795 + 818687 * 2 ^ 59
def prefixEnd_818687 : Nat := 4983230072969 + 3 ^ 40 * 818687 * 2
def baseEnd_818687 : Nat := 420379936587543617047433

theorem tailTrace_818687 : CollatzResearch.WordTrace tailWord_818687 prefixEnd_818687 420379936587543617047433 := by
  unfold tailWord_818687
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859967985044294453022315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906645323362862968681543 29859967985044294453022315)
  ·
    refine ⟨44789951977566441679533473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29859967985044294453022315 44789951977566441679533473)
    ·
      refine ⟨33592463983174831259650105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44789951977566441679533473 33592463983174831259650105)
      ·
        refine ⟨25194347987381123444737579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33592463983174831259650105 25194347987381123444737579)
        ·
          refine ⟨37791521981071685167106369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25194347987381123444737579 37791521981071685167106369)
          ·
            refine ⟨28343641485803763875329777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37791521981071685167106369 28343641485803763875329777)
            ·
              refine ⟨21257731114352822906497333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28343641485803763875329777 21257731114352822906497333)
              ·
                refine ⟨1992912291970577147484125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21257731114352822906497333 1992912291970577147484125)
                ·
                  refine ⟨747342109488966430306547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1992912291970577147484125 747342109488966430306547)
                  ·
                    refine ⟨1121013164233449645459821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747342109488966430306547 1121013164233449645459821)
                    ·
                      refine ⟨420379936587543617047433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121013164233449645459821 420379936587543617047433)
                      ·
                        rfl

theorem cell23_818687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_818687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818687 prefixEnd_818687 := by exact prefixLift 818687
  have htrace : WordTrace (prefixWord ++ tailWord_818687) baseStart_818687 baseEnd_818687 := by
    simpa [prefixWord, tailWord_818687, baseEnd_818687] using wordTrace_append hprefix tailTrace_818687
  have hstable : (prefixWord ++ tailWord_818687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818687).length < 2 ^ (prefixWord ++ tailWord_818687).sum := by decide
  have hdescent : baseEnd_818687 < baseStart_818687 := by decide
  rcases family_descends (prefixWord ++ tailWord_818687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818697 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 4, 3, 2]
def baseStart_818697 : Nat := 118140960795 + 818697 * 2 ^ 59
def prefixEnd_818697 : Nat := 4983230072969 + 3 ^ 40 * 818697 * 2
def baseEnd_818697 : Nat := 420385071394088577922387

theorem tailTrace_818697 : CollatzResearch.WordTrace tailWord_818697 prefixEnd_818697 420385071394088577922387 := by
  unfold tailWord_818697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29860332715008066160886345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906888476672044107257563 29860332715008066160886345)
  ·
    refine ⟨22395249536256049620664759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29860332715008066160886345 22395249536256049620664759)
    ·
      refine ⟨33592874304384074430997139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22395249536256049620664759 33592874304384074430997139)
      ·
        refine ⟨50389311456576111646495709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33592874304384074430997139 50389311456576111646495709)
        ·
          refine ⟨18895991796216041867435891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50389311456576111646495709 18895991796216041867435891)
          ·
            refine ⟨28343987694324062801153837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18895991796216041867435891 28343987694324062801153837)
            ·
              refine ⟨10628995385371523550432689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28343987694324062801153837 10628995385371523550432689)
              ·
                refine ⟨7971746539028642662824517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10628995385371523550432689 7971746539028642662824517)
                ·
                  refine ⟨1494702476067870499279597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7971746539028642662824517 1494702476067870499279597)
                  ·
                    refine ⟨560513428525451437229849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494702476067870499279597 560513428525451437229849)
                    ·
                      refine ⟨420385071394088577922387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560513428525451437229849 420385071394088577922387)
                      ·
                        rfl

theorem cell23_818697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3, 2].length) (baseStart_818697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818697 prefixEnd_818697 := by exact prefixLift 818697
  have htrace : WordTrace (prefixWord ++ tailWord_818697) baseStart_818697 baseEnd_818697 := by
    simpa [prefixWord, tailWord_818697, baseEnd_818697] using wordTrace_append hprefix tailTrace_818697
  have hstable : (prefixWord ++ tailWord_818697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818697).length < 2 ^ (prefixWord ++ tailWord_818697).sum := by decide
  have hdescent : baseEnd_818697 < baseStart_818697 := by decide
  rcases family_descends (prefixWord ++ tailWord_818697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818707 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 1, 5]
def baseStart_818707 : Nat := 118140960795 + 818707 * 2 ^ 59
def prefixEnd_818707 : Nat := 4983230072969 + 3 ^ 40 * 818707 * 2
def baseEnd_818707 : Nat := 140130068733544512932447

theorem tailTrace_818707 : CollatzResearch.WordTrace tailWord_818707 prefixEnd_818707 140130068733544512932447 := by
  unfold tailWord_818707
  simp only [CollatzResearch.WordTrace]
  refine ⟨29860697444971837868750375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19907131629981225245833583 29860697444971837868750375)
  ·
    refine ⟨44791046167457756803125563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29860697444971837868750375 44791046167457756803125563)
    ·
      refine ⟨67186569251186635204688345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44791046167457756803125563 67186569251186635204688345)
      ·
        refine ⟨50389926938389976403516259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67186569251186635204688345 50389926938389976403516259)
        ·
          refine ⟨75584890407584964605274389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50389926938389976403516259 75584890407584964605274389)
          ·
            refine ⟨3543041737855545215872237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75584890407584964605274389 3543041737855545215872237)
            ·
              refine ⟨1328640651695829455952089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3543041737855545215872237 1328640651695829455952089)
              ·
                refine ⟨996480488771872091964067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328640651695829455952089 996480488771872091964067)
                ·
                  refine ⟨1494720733157808137946101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996480488771872091964067 1494720733157808137946101)
                  ·
                    refine ⟨140130068733544512932447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1494720733157808137946101 140130068733544512932447)
                    ·
                      rfl

theorem cell23_818707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 5].length) (baseStart_818707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818707 prefixEnd_818707 := by exact prefixLift 818707
  have htrace : WordTrace (prefixWord ++ tailWord_818707) baseStart_818707 baseEnd_818707 := by
    simpa [prefixWord, tailWord_818707, baseEnd_818707] using wordTrace_append hprefix tailTrace_818707
  have hstable : (prefixWord ++ tailWord_818707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818707).length < 2 ^ (prefixWord ++ tailWord_818707).sum := by decide
  have hdescent : baseEnd_818707 < baseStart_818707 := by decide
  rcases family_descends (prefixWord ++ tailWord_818707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818757 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_818757 : Nat := 118140960795 + 818757 * 2 ^ 59
def prefixEnd_818757 : Nat := 4983230072969 + 3 ^ 40 * 818757 * 2
def baseEnd_818757 : Nat := 420415880233358343172111

theorem tailTrace_818757 : CollatzResearch.WordTrace tailWord_818757 prefixEnd_818757 420415880233358343172111 := by
  unfold tailWord_818757
  simp only [CollatzResearch.WordTrace]
  refine ⟨29862521094790696408070525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19908347396527130938713683 29862521094790696408070525)
  ·
    refine ⟨11198445410546511153026447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29862521094790696408070525 11198445410546511153026447)
    ·
      refine ⟨16797668115819766729539671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198445410546511153026447 16797668115819766729539671)
      ·
        refine ⟨25196502173729650094309507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16797668115819766729539671 25196502173729650094309507)
        ·
          refine ⟨37794753260594475141464261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25196502173729650094309507 37794753260594475141464261)
          ·
            refine ⟨7086516236361464089024549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37794753260594475141464261 7086516236361464089024549)
            ·
              refine ⟨1328721794317774516692103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7086516236361464089024549 1328721794317774516692103)
              ·
                refine ⟨1993082691476661775038155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328721794317774516692103 1993082691476661775038155)
                ·
                  refine ⟨2989624037214992662557233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993082691476661775038155 2989624037214992662557233)
                  ·
                    refine ⟨2242218027911244496917925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2989624037214992662557233 2242218027911244496917925)
                    ·
                      refine ⟨420415880233358343172111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2242218027911244496917925 420415880233358343172111)
                      ·
                        rfl

theorem cell23_818757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_818757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818757 prefixEnd_818757 := by exact prefixLift 818757
  have htrace : WordTrace (prefixWord ++ tailWord_818757) baseStart_818757 baseEnd_818757 := by
    simpa [prefixWord, tailWord_818757, baseEnd_818757] using wordTrace_append hprefix tailTrace_818757
  have hstable : (prefixWord ++ tailWord_818757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818757).length < 2 ^ (prefixWord ++ tailWord_818757).sum := by decide
  have hdescent : baseEnd_818757 < baseStart_818757 := by decide
  rcases family_descends (prefixWord ++ tailWord_818757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818765 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_818765 : Nat := 118140960795 + 818765 * 2 ^ 59
def prefixEnd_818765 : Nat := 4983230072969 + 3 ^ 40 * 818765 * 2
def baseEnd_818765 : Nat := 420419988078594311872075

theorem tailTrace_818765 : CollatzResearch.WordTrace tailWord_818765 prefixEnd_818765 420419988078594311872075 := by
  unfold tailWord_818765
  simp only [CollatzResearch.WordTrace]
  refine ⟨29862812878761713774361749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19908541919174475849574499 29862812878761713774361749)
  ·
    refine ⟨1399819353691955333173207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29862812878761713774361749 1399819353691955333173207)
    ·
      refine ⟨2099729030537932999759811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399819353691955333173207 2099729030537932999759811)
      ·
        refine ⟨3149593545806899499639717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099729030537932999759811 3149593545806899499639717)
        ·
          refine ⟨590548789838793656182447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3149593545806899499639717 590548789838793656182447)
          ·
            refine ⟨885823184758190484273671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590548789838793656182447 885823184758190484273671)
            ·
              refine ⟨1328734777137285726410507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885823184758190484273671 1328734777137285726410507)
              ·
                refine ⟨1993102165705928589615761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328734777137285726410507 1993102165705928589615761)
                ·
                  refine ⟨1494826624279446442211821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993102165705928589615761 1494826624279446442211821)
                  ·
                    refine ⟨560559984104792415829433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494826624279446442211821 560559984104792415829433)
                    ·
                      refine ⟨420419988078594311872075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560559984104792415829433 420419988078594311872075)
                      ·
                        rfl

theorem cell23_818765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_818765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818765 prefixEnd_818765 := by exact prefixLift 818765
  have htrace : WordTrace (prefixWord ++ tailWord_818765) baseStart_818765 baseEnd_818765 := by
    simpa [prefixWord, tailWord_818765, baseEnd_818765] using wordTrace_append hprefix tailTrace_818765
  have hstable : (prefixWord ++ tailWord_818765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818765).length < 2 ^ (prefixWord ++ tailWord_818765).sum := by decide
  have hdescent : baseEnd_818765 < baseStart_818765 := by decide
  rcases family_descends (prefixWord ++ tailWord_818765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818810 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_818810 : Nat := 118140960795 + 818810 * 2 ^ 59
def prefixEnd_818810 : Nat := 4983230072969 + 3 ^ 40 * 818810 * 2
def baseEnd_818810 : Nat := 140147698236015545269789

theorem tailTrace_818810 : CollatzResearch.WordTrace tailWord_818810 prefixEnd_818810 140147698236015545269789 := by
  unfold tailWord_818810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466113540899671614937471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19909636109065790973166589 7466113540899671614937471)
  ·
    refine ⟨11199170311349507422406207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466113540899671614937471 11199170311349507422406207)
    ·
      refine ⟨16798755467024261133609311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11199170311349507422406207 16798755467024261133609311)
      ·
        refine ⟨25198133200536391700413967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16798755467024261133609311 25198133200536391700413967)
        ·
          refine ⟨37797199800804587550620951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25198133200536391700413967 37797199800804587550620951)
          ·
            refine ⟨56695799701206881325931427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37797199800804587550620951 56695799701206881325931427)
            ·
              refine ⟨85043699551810321988897141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56695799701206881325931427 85043699551810321988897141)
              ·
                refine ⟨7972846832982217686459107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85043699551810321988897141 7972846832982217686459107)
                ·
                  refine ⟨11959270249473326529688661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972846832982217686459107 11959270249473326529688661)
                  ·
                    refine ⟨140147698236015545269789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11959270249473326529688661 140147698236015545269789)
                    ·
                      rfl

theorem cell23_818810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_818810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818810 prefixEnd_818810 := by exact prefixLift 818810
  have htrace : WordTrace (prefixWord ++ tailWord_818810) baseStart_818810 baseEnd_818810 := by
    simpa [prefixWord, tailWord_818810, baseEnd_818810] using wordTrace_append hprefix tailTrace_818810
  have hstable : (prefixWord ++ tailWord_818810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818810).length < 2 ^ (prefixWord ++ tailWord_818810).sum := by decide
  have hdescent : baseEnd_818810 < baseStart_818810 := by decide
  rcases family_descends (prefixWord ++ tailWord_818810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818811 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 2, 1, 3]
def baseStart_818811 : Nat := 118140960795 + 818811 * 2 ^ 59
def prefixEnd_818811 : Nat := 4983230072969 + 3 ^ 40 * 818811 * 2
def baseEnd_818811 : Nat := 420443608188701131896863

theorem tailTrace_818811 : CollatzResearch.WordTrace tailWord_818811 prefixEnd_818811 420443608188701131896863 := by
  unfold tailWord_818811
  simp only [CollatzResearch.WordTrace]
  refine ⟨29864490636595063630536287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19909660424396709087024191 29864490636595063630536287)
  ·
    refine ⟨44796735954892595445804431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29864490636595063630536287 44796735954892595445804431)
    ·
      refine ⟨67195103932338893168706647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44796735954892595445804431 67195103932338893168706647)
      ·
        refine ⟨100792655898508339753059971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67195103932338893168706647 100792655898508339753059971)
        ·
          refine ⟨151188983847762509629589957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100792655898508339753059971 151188983847762509629589957)
          ·
            refine ⟨28347934471455470555548117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151188983847762509629589957 28347934471455470555548117)
            ·
              refine ⟨664404714174737591145659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28347934471455470555548117 664404714174737591145659)
              ·
                refine ⟨996607071262106386718489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664404714174737591145659 996607071262106386718489)
                ·
                  refine ⟨747455303446579790038867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996607071262106386718489 747455303446579790038867)
                  ·
                    refine ⟨1121182955169869685058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747455303446579790038867 1121182955169869685058301)
                    ·
                      refine ⟨420443608188701131896863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121182955169869685058301 420443608188701131896863)
                      ·
                        rfl

theorem cell23_818811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 1, 3].length) (baseStart_818811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818811 prefixEnd_818811 := by exact prefixLift 818811
  have htrace : WordTrace (prefixWord ++ tailWord_818811) baseStart_818811 baseEnd_818811 := by
    simpa [prefixWord, tailWord_818811, baseEnd_818811] using wordTrace_append hprefix tailTrace_818811
  have hstable : (prefixWord ++ tailWord_818811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818811).length < 2 ^ (prefixWord ++ tailWord_818811).sum := by decide
  have hdescent : baseEnd_818811 < baseStart_818811 := by decide
  rcases family_descends (prefixWord ++ tailWord_818811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818821 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_818821 : Nat := 118140960795 + 818821 * 2 ^ 59
def prefixEnd_818821 : Nat := 4983230072969 + 3 ^ 40 * 818821 * 2
def baseEnd_818821 : Nat := 420448742995246092771817

theorem tailTrace_818821 : CollatzResearch.WordTrace tailWord_818821 prefixEnd_818821 420448742995246092771817 := by
  unfold tailWord_818821
  simp only [CollatzResearch.WordTrace]
  refine ⟨29864855366558835338400317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19909903577705890225600211 29864855366558835338400317)
  ·
    refine ⟨11199320762459563251900119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29864855366558835338400317 11199320762459563251900119)
    ·
      refine ⟨16798981143689344877850179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11199320762459563251900119 16798981143689344877850179)
      ·
        refine ⟨25198471715534017316775269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16798981143689344877850179 25198471715534017316775269)
        ·
          refine ⟨4724713446662628246895363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25198471715534017316775269 4724713446662628246895363)
          ·
            refine ⟨7087070169993942370343045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724713446662628246895363 7087070169993942370343045)
            ·
              refine ⟨1328825656873864194439321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7087070169993942370343045 1328825656873864194439321)
              ·
                refine ⟨996619242655398145829491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328825656873864194439321 996619242655398145829491)
                ·
                  refine ⟨1494928863983097218744237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996619242655398145829491 1494928863983097218744237)
                  ·
                    refine ⟨560598323993661457029089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494928863983097218744237 560598323993661457029089)
                    ·
                      refine ⟨420448742995246092771817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560598323993661457029089 420448742995246092771817)
                      ·
                        rfl

theorem cell23_818821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_818821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818821 prefixEnd_818821 := by exact prefixLift 818821
  have htrace : WordTrace (prefixWord ++ tailWord_818821) baseStart_818821 baseEnd_818821 := by
    simpa [prefixWord, tailWord_818821, baseEnd_818821] using wordTrace_append hprefix tailTrace_818821
  have hstable : (prefixWord ++ tailWord_818821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818821).length < 2 ^ (prefixWord ++ tailWord_818821).sum := by decide
  have hdescent : baseEnd_818821 < baseStart_818821 := by decide
  rcases family_descends (prefixWord ++ tailWord_818821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818851 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 2, 2, 2]
def baseStart_818851 : Nat := 118140960795 + 818851 * 2 ^ 59
def prefixEnd_818851 : Nat := 4983230072969 + 3 ^ 40 * 818851 * 2
def baseEnd_818851 : Nat := 420464147414880975396679

theorem tailTrace_818851 : CollatzResearch.WordTrace tailWord_818851 prefixEnd_818851 420464147414880975396679 := by
  unfold tailWord_818851
  simp only [CollatzResearch.WordTrace]
  refine ⟨29865949556450150461992407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19910633037633433641328271 29865949556450150461992407)
  ·
    refine ⟨44798924334675225692988611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29865949556450150461992407 44798924334675225692988611)
    ·
      refine ⟨67198386502012838539482917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44798924334675225692988611 67198386502012838539482917)
      ·
        refine ⟨12599697469127407226153047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67198386502012838539482917 12599697469127407226153047)
        ·
          refine ⟨18899546203691110839229571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12599697469127407226153047 18899546203691110839229571)
          ·
            refine ⟨28349319305536666258844357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18899546203691110839229571 28349319305536666258844357)
            ·
              refine ⟨5315497369788124923533317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28349319305536666258844357 5315497369788124923533317)
              ·
                refine ⟨996655756835273423162497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5315497369788124923533317 996655756835273423162497)
                ·
                  refine ⟨747491817626455067371873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996655756835273423162497 747491817626455067371873)
                  ·
                    refine ⟨560618863219841300528905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747491817626455067371873 560618863219841300528905)
                    ·
                      refine ⟨420464147414880975396679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560618863219841300528905 420464147414880975396679)
                      ·
                        rfl

theorem cell23_818851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_818851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818851 prefixEnd_818851 := by exact prefixLift 818851
  have htrace : WordTrace (prefixWord ++ tailWord_818851) baseStart_818851 baseEnd_818851 := by
    simpa [prefixWord, tailWord_818851, baseEnd_818851] using wordTrace_append hprefix tailTrace_818851
  have hstable : (prefixWord ++ tailWord_818851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818851).length < 2 ^ (prefixWord ++ tailWord_818851).sum := by decide
  have hdescent : baseEnd_818851 < baseStart_818851 := by decide
  rcases family_descends (prefixWord ++ tailWord_818851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818862 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_818862 : Nat := 118140960795 + 818862 * 2 ^ 59
def prefixEnd_818862 : Nat := 4983230072969 + 3 ^ 40 * 818862 * 2
def baseEnd_818862 : Nat := 420469795702080432359129

theorem tailTrace_818862 : CollatzResearch.WordTrace tailWord_818862 prefixEnd_818862 420469795702080432359129 := by
  unfold tailWord_818862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733293844926287417580355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19910900506273532893761893 3733293844926287417580355)
  ·
    refine ⟨5599940767389431126370533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733293844926287417580355 5599940767389431126370533)
    ·
      refine ⟨1049988893885518336194475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5599940767389431126370533 1049988893885518336194475)
      ·
        refine ⟨1574983340828277504291713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049988893885518336194475 1574983340828277504291713)
        ·
          refine ⟨1181237505621208128218785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574983340828277504291713 1181237505621208128218785)
          ·
            refine ⟨885928129215906096164089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181237505621208128218785 885928129215906096164089)
            ·
              refine ⟨664446096911929572123067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885928129215906096164089 664446096911929572123067)
              ·
                refine ⟨996669145367894358184601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664446096911929572123067 996669145367894358184601)
                ·
                  refine ⟨747501859025920768638451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996669145367894358184601 747501859025920768638451)
                  ·
                    refine ⟨1121252788538881152957677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747501859025920768638451 1121252788538881152957677)
                    ·
                      refine ⟨420469795702080432359129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121252788538881152957677 420469795702080432359129)
                      ·
                        rfl

theorem cell23_818862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_818862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818862 prefixEnd_818862 := by exact prefixLift 818862
  have htrace : WordTrace (prefixWord ++ tailWord_818862) baseStart_818862 baseEnd_818862 := by
    simpa [prefixWord, tailWord_818862, baseEnd_818862] using wordTrace_append hprefix tailTrace_818862
  have hstable : (prefixWord ++ tailWord_818862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818862).length < 2 ^ (prefixWord ++ tailWord_818862).sum := by decide
  have hdescent : baseEnd_818862 < baseStart_818862 := by decide
  rcases family_descends (prefixWord ++ tailWord_818862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818867 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3]
def baseStart_818867 : Nat := 118140960795 + 818867 * 2 ^ 59
def prefixEnd_818867 : Nat := 4983230072969 + 3 ^ 40 * 818867 * 2
def baseEnd_818867 : Nat := 420472363105352912796605

theorem tailTrace_818867 : CollatzResearch.WordTrace tailWord_818867 prefixEnd_818867 420472363105352912796605 := by
  unfold tailWord_818867
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866533124392185194574855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19911022082928123463049903 29866533124392185194574855)
  ·
    refine ⟨44799799686588277791862283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29866533124392185194574855 44799799686588277791862283)
    ·
      refine ⟨67199699529882416687793425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44799799686588277791862283 67199699529882416687793425)
      ·
        refine ⟨50399774647411812515845069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67199699529882416687793425 50399774647411812515845069)
        ·
          refine ⟨18899915492779429693441901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50399774647411812515845069 18899915492779429693441901)
          ·
            refine ⟨7087468309792286135040713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18899915492779429693441901 7087468309792286135040713)
            ·
              refine ⟨5315601232344214601280535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7087468309792286135040713 5315601232344214601280535)
              ·
                refine ⟨7973401848516321901920803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315601232344214601280535 7973401848516321901920803)
                ·
                  refine ⟨11960102772774482852881205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973401848516321901920803 11960102772774482852881205)
                  ·
                    refine ⟨1121259634947607767457613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11960102772774482852881205 1121259634947607767457613)
                    ·
                      refine ⟨420472363105352912796605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121259634947607767457613 420472363105352912796605)
                      ·
                        rfl

theorem cell23_818867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_818867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818867 prefixEnd_818867 := by exact prefixLift 818867
  have htrace : WordTrace (prefixWord ++ tailWord_818867) baseStart_818867 baseEnd_818867 := by
    simpa [prefixWord, tailWord_818867, baseEnd_818867] using wordTrace_append hprefix tailTrace_818867
  have hstable : (prefixWord ++ tailWord_818867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818867).length < 2 ^ (prefixWord ++ tailWord_818867).sum := by decide
  have hdescent : baseEnd_818867 < baseStart_818867 := by decide
  rcases family_descends (prefixWord ++ tailWord_818867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818897 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_818897 : Nat := 118140960795 + 818897 * 2 ^ 59
def prefixEnd_818897 : Nat := 4983230072969 + 3 ^ 40 * 818897 * 2
def baseEnd_818897 : Nat := 420487767524987795421467

theorem tailTrace_818897 : CollatzResearch.WordTrace tailWord_818897 prefixEnd_818897 420487767524987795421467 := by
  unfold tailWord_818897
  simp only [CollatzResearch.WordTrace]
  refine ⟨29867627314283500318166945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19911751542855666878777963 29867627314283500318166945)
  ·
    refine ⟨22400720485712625238625209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29867627314283500318166945 22400720485712625238625209)
    ·
      refine ⟨16800540364284468928968907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22400720485712625238625209 16800540364284468928968907)
      ·
        refine ⟨25200810546426703393453361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800540364284468928968907 25200810546426703393453361)
        ·
          refine ⟨18900607909820027545090021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25200810546426703393453361 18900607909820027545090021)
          ·
            refine ⟨3543863983091255164704379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18900607909820027545090021 3543863983091255164704379)
            ·
              refine ⟨5315795974636882747056569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543863983091255164704379 5315795974636882747056569)
              ·
                refine ⟨3986846980977662060292427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315795974636882747056569 3986846980977662060292427)
                ·
                  refine ⟨5980270471466493090438641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986846980977662060292427 5980270471466493090438641)
                  ·
                    refine ⟨4485202853599869817828981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980270471466493090438641 4485202853599869817828981)
                    ·
                      refine ⟨420487767524987795421467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4485202853599869817828981 420487767524987795421467)
                      ·
                        rfl

theorem cell23_818897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_818897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818897 prefixEnd_818897 := by exact prefixLift 818897
  have htrace : WordTrace (prefixWord ++ tailWord_818897) baseStart_818897 baseEnd_818897 := by
    simpa [prefixWord, tailWord_818897, baseEnd_818897] using wordTrace_append hprefix tailTrace_818897
  have hstable : (prefixWord ++ tailWord_818897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818897).length < 2 ^ (prefixWord ++ tailWord_818897).sum := by decide
  have hdescent : baseEnd_818897 < baseStart_818897 := by decide
  rcases family_descends (prefixWord ++ tailWord_818897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818908 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 5]
def baseStart_818908 : Nat := 118140960795 + 818908 * 2 ^ 59
def prefixEnd_818908 : Nat := 4983230072969 + 3 ^ 40 * 818908 * 2
def baseEnd_818908 : Nat := 46721490645798583598213

theorem tailTrace_818908 : CollatzResearch.WordTrace tailWord_818908 prefixEnd_818908 46721490645798583598213 := by
  unfold tailWord_818908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14934014258621824598408689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19912019011495766131211585 14934014258621824598408689)
  ·
    refine ⟨11200510693966368448806517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14934014258621824598408689 11200510693966368448806517)
    ·
      refine ⟨1050047877559347042075611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11200510693966368448806517 1050047877559347042075611)
      ·
        refine ⟨1575071816339020563113417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050047877559347042075611 1575071816339020563113417)
        ·
          refine ⟨1181303862254265422335063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575071816339020563113417 1181303862254265422335063)
          ·
            refine ⟨1771955793381398133502595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181303862254265422335063 1771955793381398133502595)
            ·
              refine ⟨2657933690072097200253893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771955793381398133502595 2657933690072097200253893)
              ·
                refine ⟨498362566888518225047605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2657933690072097200253893 498362566888518225047605)
                ·
                  refine ⟨46721490645798583598213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498362566888518225047605 46721490645798583598213)
                  ·
                    rfl

theorem cell23_818908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_818908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818908 prefixEnd_818908 := by exact prefixLift 818908
  have htrace : WordTrace (prefixWord ++ tailWord_818908) baseStart_818908 baseEnd_818908 := by
    simpa [prefixWord, tailWord_818908, baseEnd_818908] using wordTrace_append hprefix tailTrace_818908
  have hstable : (prefixWord ++ tailWord_818908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818908).length < 2 ^ (prefixWord ++ tailWord_818908).sum := by decide
  have hdescent : baseEnd_818908 < baseStart_818908 := by decide
  rcases family_descends (prefixWord ++ tailWord_818908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818924 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_818924 : Nat := 118140960795 + 818924 * 2 ^ 59
def prefixEnd_818924 : Nat := 4983230072969 + 3 ^ 40 * 818924 * 2
def baseEnd_818924 : Nat := 420501631502659189783843

theorem tailTrace_818924 : CollatzResearch.WordTrace tailWord_818924 prefixEnd_818924 420501631502659189783843 := by
  unfold tailWord_818924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14934306042592841964699913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19912408056790455952933217 14934306042592841964699913)
  ·
    refine ⟨11200729531944631473524935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14934306042592841964699913 11200729531944631473524935)
    ·
      refine ⟨16801094297916947210287403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200729531944631473524935 16801094297916947210287403)
      ·
        refine ⟨25201641446875420815431105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16801094297916947210287403 25201641446875420815431105)
        ·
          refine ⟨18901231085156565611573329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25201641446875420815431105 18901231085156565611573329)
          ·
            refine ⟨14175923313867424208679997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18901231085156565611573329 14175923313867424208679997)
            ·
              refine ⟨5315971242700284078254999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14175923313867424208679997 5315971242700284078254999)
              ·
                refine ⟨7973956864050426117382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315971242700284078254999 7973956864050426117382499)
                ·
                  refine ⟨11960935296075639176073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973956864050426117382499 11960935296075639176073749)
                  ·
                    refine ⟨560668842003545586378457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11960935296075639176073749 560668842003545586378457)
                    ·
                      refine ⟨420501631502659189783843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560668842003545586378457 420501631502659189783843)
                      ·
                        rfl

theorem cell23_818924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_818924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818924 prefixEnd_818924 := by exact prefixLift 818924
  have htrace : WordTrace (prefixWord ++ tailWord_818924) baseStart_818924 baseEnd_818924 := by
    simpa [prefixWord, tailWord_818924, baseEnd_818924] using wordTrace_append hprefix tailTrace_818924
  have hstable : (prefixWord ++ tailWord_818924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818924).length < 2 ^ (prefixWord ++ tailWord_818924).sum := by decide
  have hdescent : baseEnd_818924 < baseStart_818924 := by decide
  rcases family_descends (prefixWord ++ tailWord_818924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818981 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 6]
def baseStart_818981 : Nat := 118140960795 + 818981 * 2 ^ 59
def prefixEnd_818981 : Nat := 4983230072969 + 3 ^ 40 * 818981 * 2
def baseEnd_818981 : Nat := 46725655544440607419009

theorem tailTrace_818981 : CollatzResearch.WordTrace tailWord_818981 prefixEnd_818981 46725655544440607419009 := by
  unfold tailWord_818981
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870691045979182664224797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19913794030652788442816531 29870691045979182664224797)
  ·
    refine ⟨11201509142242193499084299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29870691045979182664224797 11201509142242193499084299)
    ·
      refine ⟨16802263713363290248626449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11201509142242193499084299 16802263713363290248626449)
      ·
        refine ⟨12601697785022467686469837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16802263713363290248626449 12601697785022467686469837)
        ·
          refine ⟨4725636669383425382426189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12601697785022467686469837 4725636669383425382426189)
          ·
            refine ⟨1772113751018784518409821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4725636669383425382426189 1772113751018784518409821)
            ·
              refine ⟨664542656632044194403683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1772113751018784518409821 664542656632044194403683)
              ·
                refine ⟨996813984948066291605525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664542656632044194403683 996813984948066291605525)
                ·
                  refine ⟨46725655544440607419009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 996813984948066291605525 46725655544440607419009)
                  ·
                    rfl

theorem cell23_818981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_818981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_818981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_818981 prefixEnd_818981 := by exact prefixLift 818981
  have htrace : WordTrace (prefixWord ++ tailWord_818981) baseStart_818981 baseEnd_818981 := by
    simpa [prefixWord, tailWord_818981, baseEnd_818981] using wordTrace_append hprefix tailTrace_818981
  have hstable : (prefixWord ++ tailWord_818981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818981).length < 2 ^ (prefixWord ++ tailWord_818981).sum := by decide
  have hdescent : baseEnd_818981 < baseStart_818981 := by decide
  rcases family_descends (prefixWord ++ tailWord_818981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819034 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_819034 : Nat := 118140960795 + 819034 * 2 ^ 59
def prefixEnd_819034 : Nat := 4983230072969 + 3 ^ 40 * 819034 * 2
def baseEnd_819034 : Nat := 420558114374653759408337

theorem tailTrace_819034 : CollatzResearch.WordTrace tailWord_819034 prefixEnd_819034 420558114374653759408337 := by
  unfold tailWord_819034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468156028696793178976039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19915082743191448477269437 7468156028696793178976039)
  ·
    refine ⟨11202234043045189768464059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468156028696793178976039 11202234043045189768464059)
    ·
      refine ⟨16803351064567784652696089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11202234043045189768464059 16803351064567784652696089)
      ·
        refine ⟨12602513298425838489522067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16803351064567784652696089 12602513298425838489522067)
        ·
          refine ⟨18903769947638757734283101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12602513298425838489522067 18903769947638757734283101)
          ·
            refine ⟨7088913730364534150356163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18903769947638757734283101 7088913730364534150356163)
            ·
              refine ⟨10633370595546801225534245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088913730364534150356163 10633370595546801225534245)
              ·
                refine ⟨1993756986665025229787671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10633370595546801225534245 1993756986665025229787671)
                ·
                  refine ⟨2990635479997537844681507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993756986665025229787671 2990635479997537844681507)
                  ·
                    refine ⟨4485953219996306767022261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990635479997537844681507 4485953219996306767022261)
                    ·
                      refine ⟨420558114374653759408337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4485953219996306767022261 420558114374653759408337)
                      ·
                        rfl

theorem cell23_819034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_819034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819034 prefixEnd_819034 := by exact prefixLift 819034
  have htrace : WordTrace (prefixWord ++ tailWord_819034) baseStart_819034 baseEnd_819034 := by
    simpa [prefixWord, tailWord_819034, baseEnd_819034] using wordTrace_append hprefix tailTrace_819034
  have hstable : (prefixWord ++ tailWord_819034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819034).length < 2 ^ (prefixWord ++ tailWord_819034).sum := by decide
  have hdescent : baseEnd_819034 < baseStart_819034 := by decide
  rcases family_descends (prefixWord ++ tailWord_819034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819041 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_819041 : Nat := 118140960795 + 819041 * 2 ^ 59
def prefixEnd_819041 : Nat := 4983230072969 + 3 ^ 40 * 819041 * 2
def baseEnd_819041 : Nat := 140187236246411744006935

theorem tailTrace_819041 : CollatzResearch.WordTrace tailWord_819041 prefixEnd_819041 140187236246411744006935 := by
  unfold tailWord_819041
  simp only [CollatzResearch.WordTrace]
  refine ⟨29872879425761812911408977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19915252950507875274272651 29872879425761812911408977)
  ·
    refine ⟨22404659569321359683556733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29872879425761812911408977 22404659569321359683556733)
    ·
      refine ⟨8401747338495509881333775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22404659569321359683556733 8401747338495509881333775)
      ·
        refine ⟨12602621007743264822000663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401747338495509881333775 12602621007743264822000663)
        ·
          refine ⟨18903931511614897233000995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12602621007743264822000663 18903931511614897233000995)
          ·
            refine ⟨28355897267422345849501493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18903931511614897233000995 28355897267422345849501493)
            ·
              refine ⟨2658365368820844923390765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28355897267422345849501493 2658365368820844923390765)
              ·
                refine ⟨996887013307816846271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2658365368820844923390765 996887013307816846271537)
                ·
                  refine ⟨747665259980862634703653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996887013307816846271537 747665259980862634703653)
                  ·
                    refine ⟨140187236246411744006935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 747665259980862634703653 140187236246411744006935)
                    ·
                      rfl

theorem cell23_819041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_819041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819041 prefixEnd_819041 := by exact prefixLift 819041
  have htrace : WordTrace (prefixWord ++ tailWord_819041) baseStart_819041 baseEnd_819041 := by
    simpa [prefixWord, tailWord_819041, baseEnd_819041] using wordTrace_append hprefix tailTrace_819041
  have hstable : (prefixWord ++ tailWord_819041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819041).length < 2 ^ (prefixWord ++ tailWord_819041).sum := by decide
  have hdescent : baseEnd_819041 < baseStart_819041 := by decide
  rcases family_descends (prefixWord ++ tailWord_819041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819048 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_819048 : Nat := 118140960795 + 819048 * 2 ^ 59
def prefixEnd_819048 : Nat := 4983230072969 + 3 ^ 40 * 819048 * 2
def baseEnd_819048 : Nat := 420565303103816704633273

theorem tailTrace_819048 : CollatzResearch.WordTrace tailWord_819048 prefixEnd_819048 420565303103816704633273 := by
  unfold tailWord_819048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14936567368368226553456899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19915423157824302071275865 14936567368368226553456899)
  ·
    refine ⟨22404851052552339830185349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14936567368368226553456899 22404851052552339830185349)
    ·
      refine ⟨4200909572353563718159753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22404851052552339830185349 4200909572353563718159753)
      ·
        refine ⟨3150682179265172788619815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4200909572353563718159753 3150682179265172788619815)
        ·
          refine ⟨4726023268897759182929723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150682179265172788619815 4726023268897759182929723)
          ·
            refine ⟨7089034903346638774394585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726023268897759182929723 7089034903346638774394585)
            ·
              refine ⟨5316776177509979080795939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089034903346638774394585 5316776177509979080795939)
              ·
                refine ⟨7975164266264968621193909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316776177509979080795939 7975164266264968621193909)
                ·
                  refine ⟨747671649962340808236929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7975164266264968621193909 747671649962340808236929)
                  ·
                    refine ⟨560753737471755606177697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747671649962340808236929 560753737471755606177697)
                    ·
                      refine ⟨420565303103816704633273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560753737471755606177697 420565303103816704633273)
                      ·
                        rfl

theorem cell23_819048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_819048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819048 prefixEnd_819048 := by exact prefixLift 819048
  have htrace : WordTrace (prefixWord ++ tailWord_819048) baseStart_819048 baseEnd_819048 := by
    simpa [prefixWord, tailWord_819048, baseEnd_819048] using wordTrace_append hprefix tailTrace_819048
  have hstable : (prefixWord ++ tailWord_819048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819048).length < 2 ^ (prefixWord ++ tailWord_819048).sum := by decide
  have hdescent : baseEnd_819048 < baseStart_819048 := by decide
  rcases family_descends (prefixWord ++ tailWord_819048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819061 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_819061 : Nat := 118140960795 + 819061 * 2 ^ 59
def prefixEnd_819061 : Nat := 4983230072969 + 3 ^ 40 * 819061 * 2
def baseEnd_819061 : Nat := 420571978352325153770713

theorem tailTrace_819061 : CollatzResearch.WordTrace tailWord_819061 prefixEnd_819061 420571978352325153770713 := by
  unfold tailWord_819061
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873608885689356327137037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19915739257126237551424691 29873608885689356327137037)
  ·
    refine ⟨11202603332133508622676389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29873608885689356327137037 11202603332133508622676389)
    ·
      refine ⟨2100488124775032866751823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11202603332133508622676389 2100488124775032866751823)
      ·
        refine ⟨3150732187162549300127735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100488124775032866751823 3150732187162549300127735)
        ·
          refine ⟨4726098280743823950191603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150732187162549300127735 4726098280743823950191603)
          ·
            refine ⟨7089147421115735925287405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726098280743823950191603 7089147421115735925287405)
            ·
              refine ⟨2658430282918400971982777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7089147421115735925287405 2658430282918400971982777)
              ·
                refine ⟨1993822712188800728987083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658430282918400971982777 1993822712188800728987083)
                ·
                  refine ⟨2990734068283201093480625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993822712188800728987083 2990734068283201093480625)
                  ·
                    refine ⟨2243050551212400820110469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2990734068283201093480625 2243050551212400820110469)
                    ·
                      refine ⟨420571978352325153770713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2243050551212400820110469 420571978352325153770713)
                      ·
                        rfl

theorem cell23_819061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_819061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819061 prefixEnd_819061 := by exact prefixLift 819061
  have htrace : WordTrace (prefixWord ++ tailWord_819061) baseStart_819061 baseEnd_819061 := by
    simpa [prefixWord, tailWord_819061, baseEnd_819061] using wordTrace_append hprefix tailTrace_819061
  have hstable : (prefixWord ++ tailWord_819061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819061).length < 2 ^ (prefixWord ++ tailWord_819061).sum := by decide
  have hdescent : baseEnd_819061 < baseStart_819061 := by decide
  rcases family_descends (prefixWord ++ tailWord_819061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819065 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 1, 2, 2]
def baseStart_819065 : Nat := 118140960795 + 819065 * 2 ^ 59
def prefixEnd_819065 : Nat := 4983230072969 + 3 ^ 40 * 819065 * 2
def baseEnd_819065 : Nat := 420574032274943138120695

theorem tailTrace_819065 : CollatzResearch.WordTrace tailWord_819065 prefixEnd_819065 420574032274943138120695 := by
  unfold tailWord_819065
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873754777674865010282649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19915836518449910006855099 29873754777674865010282649)
  ·
    refine ⟨22405316083256148757711987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873754777674865010282649 22405316083256148757711987)
    ·
      refine ⟨33607974124884223136567981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22405316083256148757711987 33607974124884223136567981)
      ·
        refine ⟨12602990296831583676212993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33607974124884223136567981 12602990296831583676212993)
        ·
          refine ⟨9452242722623687757159745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12602990296831583676212993 9452242722623687757159745)
          ·
            refine ⟨7089182041967765817869809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9452242722623687757159745 7089182041967765817869809)
            ·
              refine ⟨5316886531475824363402357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089182041967765817869809 5316886531475824363402357)
              ·
                refine ⟨498458112325858534068971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5316886531475824363402357 498458112325858534068971)
                ·
                  refine ⟨747687168488787801103457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498458112325858534068971 747687168488787801103457)
                  ·
                    refine ⟨560765376366590850827593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747687168488787801103457 560765376366590850827593)
                    ·
                      refine ⟨420574032274943138120695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560765376366590850827593 420574032274943138120695)
                      ·
                        rfl

theorem cell23_819065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_819065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819065 prefixEnd_819065 := by exact prefixLift 819065
  have htrace : WordTrace (prefixWord ++ tailWord_819065) baseStart_819065 baseEnd_819065 := by
    simpa [prefixWord, tailWord_819065, baseEnd_819065] using wordTrace_append hprefix tailTrace_819065
  have hstable : (prefixWord ++ tailWord_819065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819065).length < 2 ^ (prefixWord ++ tailWord_819065).sum := by decide
  have hdescent : baseEnd_819065 < baseStart_819065 := by decide
  rcases family_descends (prefixWord ++ tailWord_819065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819098 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_819098 : Nat := 118140960795 + 819098 * 2 ^ 59
def prefixEnd_819098 : Nat := 4983230072969 + 3 ^ 40 * 819098 * 2
def baseEnd_819098 : Nat := 420590977136541509008043

theorem tailTrace_819098 : CollatzResearch.WordTrace tailWord_819098 prefixEnd_819098 420590977136541509008043 := by
  unfold tailWord_819098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468739596638827911558487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19916638924370207764155965 7468739596638827911558487)
  ·
    refine ⟨11203109394958241867337731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468739596638827911558487 11203109394958241867337731)
    ·
      refine ⟨16804664092437362801006597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203109394958241867337731 16804664092437362801006597)
      ·
        refine ⟨3150874517332005525188737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16804664092437362801006597 3150874517332005525188737)
        ·
          refine ⟨2363155887999004143891553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150874517332005525188737 2363155887999004143891553)
          ·
            refine ⟨1772366915999253107918665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2363155887999004143891553 1772366915999253107918665)
            ·
              refine ⟨1329275186999439830938999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772366915999253107918665 1329275186999439830938999)
              ·
                refine ⟨1993912780499159746408499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329275186999439830938999 1993912780499159746408499)
                ·
                  refine ⟨2990869170748739619612749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993912780499159746408499 2990869170748739619612749)
                  ·
                    refine ⟨1121575939030777357354781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990869170748739619612749 1121575939030777357354781)
                    ·
                      refine ⟨420590977136541509008043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121575939030777357354781 420590977136541509008043)
                      ·
                        rfl

theorem cell23_819098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_819098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819098 prefixEnd_819098 := by exact prefixLift 819098
  have htrace : WordTrace (prefixWord ++ tailWord_819098) baseStart_819098 baseEnd_819098 := by
    simpa [prefixWord, tailWord_819098, baseEnd_819098] using wordTrace_append hprefix tailTrace_819098
  have hstable : (prefixWord ++ tailWord_819098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819098).length < 2 ^ (prefixWord ++ tailWord_819098).sum := by decide
  have hdescent : baseEnd_819098 < baseStart_819098 := by decide
  rcases family_descends (prefixWord ++ tailWord_819098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819104 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_819104 : Nat := 118140960795 + 819104 * 2 ^ 59
def prefixEnd_819104 : Nat := 4983230072969 + 3 ^ 40 * 819104 * 2
def baseEnd_819104 : Nat := 420594058020468485533015

theorem tailTrace_819104 : CollatzResearch.WordTrace tailWord_819104 prefixEnd_819104 420594058020468485533015 := by
  unfold tailWord_819104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937588612266787335476183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19916784816355716447301577 14937588612266787335476183)
  ·
    refine ⟨22406382918400181003214275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14937588612266787335476183 22406382918400181003214275)
    ·
      refine ⟨33609574377600271504821413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22406382918400181003214275 33609574377600271504821413)
      ·
        refine ⟨6301795195800050907154015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33609574377600271504821413 6301795195800050907154015)
        ·
          refine ⟨9452692793700076360731023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301795195800050907154015 9452692793700076360731023)
          ·
            refine ⟨14179039190550114541096535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9452692793700076360731023 14179039190550114541096535)
            ·
              refine ⟨21268558785825171811644803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14179039190550114541096535 21268558785825171811644803)
              ·
                refine ⟨31902838178737757717467205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21268558785825171811644803 31902838178737757717467205)
                ·
                  refine ⟨5981782158513329572025101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31902838178737757717467205 5981782158513329572025101)
                  ·
                    refine ⟨2243168309442498589509413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5981782158513329572025101 2243168309442498589509413)
                    ·
                      refine ⟨420594058020468485533015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2243168309442498589509413 420594058020468485533015)
                      ·
                        rfl

theorem cell23_819104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_819104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819104 prefixEnd_819104 := by exact prefixLift 819104
  have htrace : WordTrace (prefixWord ++ tailWord_819104) baseStart_819104 baseEnd_819104 := by
    simpa [prefixWord, tailWord_819104, baseEnd_819104] using wordTrace_append hprefix tailTrace_819104
  have hstable : (prefixWord ++ tailWord_819104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819104).length < 2 ^ (prefixWord ++ tailWord_819104).sum := by decide
  have hdescent : baseEnd_819104 < baseStart_819104 := by decide
  rcases family_descends (prefixWord ++ tailWord_819104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819108 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_819108 : Nat := 118140960795 + 819108 * 2 ^ 59
def prefixEnd_819108 : Nat := 4983230072969 + 3 ^ 40 * 819108 * 2
def baseEnd_819108 : Nat := 420596111943086469882997

theorem tailTrace_819108 : CollatzResearch.WordTrace tailWord_819108 prefixEnd_819108 420596111943086469882997 := by
  unfold tailWord_819108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937661558259541677048989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19916882077679388902731985 14937661558259541677048989)
  ·
    refine ⟨5601623084347328128893371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14937661558259541677048989 5601623084347328128893371)
    ·
      refine ⟨8402434626520992193340057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5601623084347328128893371 8402434626520992193340057)
      ·
        refine ⟨6301825969890744145005043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8402434626520992193340057 6301825969890744145005043)
        ·
          refine ⟨9452738954836116217507565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301825969890744145005043 9452738954836116217507565)
          ·
            refine ⟨3544777108063543581565337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9452738954836116217507565 3544777108063543581565337)
            ·
              refine ⟨2658582831047657686174003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544777108063543581565337 2658582831047657686174003)
              ·
                refine ⟨3987874246571486529261005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658582831047657686174003 3987874246571486529261005)
                ·
                  refine ⟨1495452842464307448472877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3987874246571486529261005 1495452842464307448472877)
                  ·
                    refine ⟨560794815924115293177329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495452842464307448472877 560794815924115293177329)
                    ·
                      refine ⟨420596111943086469882997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560794815924115293177329 420596111943086469882997)
                      ·
                        rfl

theorem cell23_819108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_819108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819108 prefixEnd_819108 := by exact prefixLift 819108
  have htrace : WordTrace (prefixWord ++ tailWord_819108) baseStart_819108 baseEnd_819108 := by
    simpa [prefixWord, tailWord_819108, baseEnd_819108] using wordTrace_append hprefix tailTrace_819108
  have hstable : (prefixWord ++ tailWord_819108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819108).length < 2 ^ (prefixWord ++ tailWord_819108).sum := by decide
  have hdescent : baseEnd_819108 < baseStart_819108 := by decide
  rcases family_descends (prefixWord ++ tailWord_819108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819125 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_819125 : Nat := 118140960795 + 819125 * 2 ^ 59
def prefixEnd_819125 : Nat := 4983230072969 + 3 ^ 40 * 819125 * 2
def baseEnd_819125 : Nat := 420604841114212903370419

theorem tailTrace_819125 : CollatzResearch.WordTrace tailWord_819125 prefixEnd_819125 420604841114212903370419 := by
  unfold tailWord_819125
  simp only [CollatzResearch.WordTrace]
  refine ⟨29875943157457495257466829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19917295438304996838311219 29875943157457495257466829)
  ·
    refine ⟨11203478684046560721550061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29875943157457495257466829 11203478684046560721550061)
    ·
      refine ⟨4201304506517460270581273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11203478684046560721550061 4201304506517460270581273)
      ·
        refine ⟨3150978379888095202935955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201304506517460270581273 3150978379888095202935955)
        ·
          refine ⟨4726467569832142804403933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150978379888095202935955 4726467569832142804403933)
          ·
            refine ⟨1772425338687053551651475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4726467569832142804403933 1772425338687053551651475)
            ·
              refine ⟨2658638008030580327477213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772425338687053551651475 2658638008030580327477213)
              ·
                refine ⟨996989253011467622803955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2658638008030580327477213 996989253011467622803955)
                ·
                  refine ⟨1495483879517201434205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996989253011467622803955 1495483879517201434205933)
                  ·
                    refine ⟨560806454818950537827225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495483879517201434205933 560806454818950537827225)
                    ·
                      refine ⟨420604841114212903370419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560806454818950537827225 420604841114212903370419)
                      ·
                        rfl

theorem cell23_819125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_819125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819125 prefixEnd_819125 := by exact prefixLift 819125
  have htrace : WordTrace (prefixWord ++ tailWord_819125) baseStart_819125 baseEnd_819125 := by
    simpa [prefixWord, tailWord_819125, baseEnd_819125] using wordTrace_append hprefix tailTrace_819125
  have hstable : (prefixWord ++ tailWord_819125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819125).length < 2 ^ (prefixWord ++ tailWord_819125).sum := by decide
  have hdescent : baseEnd_819125 < baseStart_819125 := by decide
  rcases family_descends (prefixWord ++ tailWord_819125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_819194 : Nat := 118140960795 + 819194 * 2 ^ 59
def prefixEnd_819194 : Nat := 4983230072969 + 3 ^ 40 * 819194 * 2
def baseEnd_819194 : Nat := 420640271279373133407601

theorem tailTrace_819194 : CollatzResearch.WordTrace tailWord_819194 prefixEnd_819194 420640271279373133407601 := by
  unfold tailWord_819194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469614948551880010432159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19918973196138346694485757 7469614948551880010432159)
  ·
    refine ⟨11204422422827820015648239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7469614948551880010432159 11204422422827820015648239)
    ·
      refine ⟨16806633634241730023472359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11204422422827820015648239 16806633634241730023472359)
      ·
        refine ⟨25209950451362595035208539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16806633634241730023472359 25209950451362595035208539)
        ·
          refine ⟨37814925677043892552812809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209950451362595035208539 37814925677043892552812809)
          ·
            refine ⟨28361194257782919414609607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37814925677043892552812809 28361194257782919414609607)
            ·
              refine ⟨42541791386674379121914411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28361194257782919414609607 42541791386674379121914411)
              ·
                refine ⟨63812687080011568682871617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42541791386674379121914411 63812687080011568682871617)
                ·
                  refine ⟨47859515310008676512153713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63812687080011568682871617 47859515310008676512153713)
                  ·
                    refine ⟨35894636482506507384115285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47859515310008676512153713 35894636482506507384115285)
                    ·
                      refine ⟨420640271279373133407601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 35894636482506507384115285 420640271279373133407601)
                      ·
                        rfl

theorem cell23_819194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_819194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819194 prefixEnd_819194 := by exact prefixLift 819194
  have htrace : WordTrace (prefixWord ++ tailWord_819194) baseStart_819194 baseEnd_819194 := by
    simpa [prefixWord, tailWord_819194, baseEnd_819194] using wordTrace_append hprefix tailTrace_819194
  have hstable : (prefixWord ++ tailWord_819194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819194).length < 2 ^ (prefixWord ++ tailWord_819194).sum := by decide
  have hdescent : baseEnd_819194 < baseStart_819194 := by decide
  rcases family_descends (prefixWord ++ tailWord_819194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819201 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_819201 : Nat := 118140960795 + 819201 * 2 ^ 59
def prefixEnd_819201 : Nat := 4983230072969 + 3 ^ 40 * 819201 * 2
def baseEnd_819201 : Nat := 420643865643954606020069

theorem tailTrace_819201 : CollatzResearch.WordTrace tailWord_819201 prefixEnd_819201 420643865643954606020069 := by
  unfold tailWord_819201
  simp only [CollatzResearch.WordTrace]
  refine ⟨29878715105182160237233457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19919143403454773491488971 29878715105182160237233457)
  ·
    refine ⟨22409036328886620177925093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29878715105182160237233457 22409036328886620177925093)
    ·
      refine ⟨4201694311666241283360955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22409036328886620177925093 4201694311666241283360955)
      ·
        refine ⟨6302541467499361925041433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201694311666241283360955 6302541467499361925041433)
        ·
          refine ⟨4726906100624521443781075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302541467499361925041433 4726906100624521443781075)
          ·
            refine ⟨7090359150936782165671613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726906100624521443781075 7090359150936782165671613)
            ·
              refine ⟨2658884681601293312126855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7090359150936782165671613 2658884681601293312126855)
              ·
                refine ⟨3988327022401939968190283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658884681601293312126855 3988327022401939968190283)
                ·
                  refine ⟨5982490533602909952285425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988327022401939968190283 5982490533602909952285425)
                  ·
                    refine ⟨4486867900202182464214069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982490533602909952285425 4486867900202182464214069)
                    ·
                      refine ⟨420643865643954606020069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4486867900202182464214069 420643865643954606020069)
                      ·
                        rfl

theorem cell23_819201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_819201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819201 prefixEnd_819201 := by exact prefixLift 819201
  have htrace : WordTrace (prefixWord ++ tailWord_819201) baseStart_819201 baseEnd_819201 := by
    simpa [prefixWord, tailWord_819201, baseEnd_819201] using wordTrace_append hprefix tailTrace_819201
  have hstable : (prefixWord ++ tailWord_819201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819201).length < 2 ^ (prefixWord ++ tailWord_819201).sum := by decide
  have hdescent : baseEnd_819201 < baseStart_819201 := by decide
  rcases family_descends (prefixWord ++ tailWord_819201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819211 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4]
def baseStart_819211 : Nat := 118140960795 + 819211 * 2 ^ 59
def prefixEnd_819211 : Nat := 4983230072969 + 3 ^ 40 * 819211 * 2
def baseEnd_819211 : Nat := 420649000450499566895023

theorem tailTrace_819211 : CollatzResearch.WordTrace tailWord_819211 prefixEnd_819211 420649000450499566895023 := by
  unfold tailWord_819211
  simp only [CollatzResearch.WordTrace]
  refine ⟨29879079835145931945097487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19919386556763954630064991 29879079835145931945097487)
  ·
    refine ⟨44818619752718897917646231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29879079835145931945097487 44818619752718897917646231)
    ·
      refine ⟨67227929629078346876469347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44818619752718897917646231 67227929629078346876469347)
      ·
        refine ⟨100841894443617520314704021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67227929629078346876469347 100841894443617520314704021)
        ·
          refine ⟨4726963802044571264751751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100841894443617520314704021 4726963802044571264751751)
          ·
            refine ⟨7090445703066856897127627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726963802044571264751751 7090445703066856897127627)
            ·
              refine ⟨10635668554600285345691441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090445703066856897127627 10635668554600285345691441)
              ·
                refine ⟨7976751415950214009268581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10635668554600285345691441 7976751415950214009268581)
                ·
                  refine ⟨1495640890490665126737859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7976751415950214009268581 1495640890490665126737859)
                  ·
                    refine ⟨2243461335735997690106789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495640890490665126737859 2243461335735997690106789)
                    ·
                      refine ⟨420649000450499566895023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2243461335735997690106789 420649000450499566895023)
                      ·
                        rfl

theorem cell23_819211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_819211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819211 prefixEnd_819211 := by exact prefixLift 819211
  have htrace : WordTrace (prefixWord ++ tailWord_819211) baseStart_819211 baseEnd_819211 := by
    simpa [prefixWord, tailWord_819211, baseEnd_819211] using wordTrace_append hprefix tailTrace_819211
  have hstable : (prefixWord ++ tailWord_819211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819211).length < 2 ^ (prefixWord ++ tailWord_819211).sum := by decide
  have hdescent : baseEnd_819211 < baseStart_819211 := by decide
  rcases family_descends (prefixWord ++ tailWord_819211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819228 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_819228 : Nat := 118140960795 + 819228 * 2 ^ 59
def prefixEnd_819228 : Nat := 4983230072969 + 3 ^ 40 * 819228 * 2
def baseEnd_819228 : Nat := 420657729621626000382445

theorem tailTrace_819228 : CollatzResearch.WordTrace tailWord_819228 prefixEnd_819228 420657729621626000382445 := by
  unfold tailWord_819228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939849938042171924233169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19919799917389562565644225 14939849938042171924233169)
  ·
    refine ⟨11204887453531628943174877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14939849938042171924233169 11204887453531628943174877)
    ·
      refine ⟨4201832795074360853690579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11204887453531628943174877 4201832795074360853690579)
      ·
        refine ⟨6302749192611541280535869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201832795074360853690579 6302749192611541280535869)
        ·
          refine ⟨2363530947229327980200951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6302749192611541280535869 2363530947229327980200951)
          ·
            refine ⟨3545296420843991970301427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363530947229327980200951 3545296420843991970301427)
            ·
              refine ⟨5317944631265987955452141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545296420843991970301427 5317944631265987955452141)
              ·
                refine ⟨1994229236724745483294553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317944631265987955452141 1994229236724745483294553)
                ·
                  refine ⟨1495671927543559112470915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994229236724745483294553 1495671927543559112470915)
                  ·
                    refine ⟨2243507891315338668706373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495671927543559112470915 2243507891315338668706373)
                    ·
                      refine ⟨420657729621626000382445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2243507891315338668706373 420657729621626000382445)
                      ·
                        rfl

theorem cell23_819228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_819228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819228 prefixEnd_819228 := by exact prefixLift 819228
  have htrace : WordTrace (prefixWord ++ tailWord_819228) baseStart_819228 baseEnd_819228 := by
    simpa [prefixWord, tailWord_819228, baseEnd_819228] using wordTrace_append hprefix tailTrace_819228
  have hstable : (prefixWord ++ tailWord_819228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819228).length < 2 ^ (prefixWord ++ tailWord_819228).sum := by decide
  have hdescent : baseEnd_819228 < baseStart_819228 := by decide
  rcases family_descends (prefixWord ++ tailWord_819228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819248 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_819248 : Nat := 118140960795 + 819248 * 2 ^ 59
def prefixEnd_819248 : Nat := 4983230072969 + 3 ^ 40 * 819248 * 2
def baseEnd_819248 : Nat := 420667999234715922132353

theorem tailTrace_819248 : CollatzResearch.WordTrace tailWord_819248 prefixEnd_819248 420667999234715922132353 := by
  unfold tailWord_819248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940214668005943632097199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19920286224007924842796265 14940214668005943632097199)
  ·
    refine ⟨22410322002008915448145799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14940214668005943632097199 22410322002008915448145799)
    ·
      refine ⟨33615483003013373172218699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22410322002008915448145799 33615483003013373172218699)
      ·
        refine ⟨50423224504520059758328049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33615483003013373172218699 50423224504520059758328049)
        ·
          refine ⟨37817418378390044818746037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50423224504520059758328049 37817418378390044818746037)
          ·
            refine ⟨3545382972974066701757441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37817418378390044818746037 3545382972974066701757441)
            ·
              refine ⟨2659037229730550026318081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545382972974066701757441 2659037229730550026318081)
              ·
                refine ⟨1994277922297912519738561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659037229730550026318081 1994277922297912519738561)
                ·
                  refine ⟨1495708441723434389803921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994277922297912519738561 1495708441723434389803921)
                  ·
                    refine ⟨1121781331292575792352941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495708441723434389803921 1121781331292575792352941)
                    ·
                      refine ⟨420667999234715922132353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121781331292575792352941 420667999234715922132353)
                      ·
                        rfl

theorem cell23_819248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_819248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819248 prefixEnd_819248 := by exact prefixLift 819248
  have htrace : WordTrace (prefixWord ++ tailWord_819248) baseStart_819248 baseEnd_819248 := by
    simpa [prefixWord, tailWord_819248, baseEnd_819248] using wordTrace_append hprefix tailTrace_819248
  have hstable : (prefixWord ++ tailWord_819248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819248).length < 2 ^ (prefixWord ++ tailWord_819248).sum := by decide
  have hdescent : baseEnd_819248 < baseStart_819248 := by decide
  rcases family_descends (prefixWord ++ tailWord_819248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819251 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 6]
def baseStart_819251 : Nat := 118140960795 + 819251 * 2 ^ 59
def prefixEnd_819251 : Nat := 4983230072969 + 3 ^ 40 * 819251 * 2
def baseEnd_819251 : Nat := 46741059964075490043871

theorem tailTrace_819251 : CollatzResearch.WordTrace tailWord_819251 prefixEnd_819251 46741059964075490043871 := by
  unfold tailWord_819251
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880538755001018776553607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19920359170000679184369071 29880538755001018776553607)
  ·
    refine ⟨44820808132501528164830411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29880538755001018776553607 44820808132501528164830411)
    ·
      refine ⟨67231212198752292247245617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44820808132501528164830411 67231212198752292247245617)
      ·
        refine ⟨50423409149064219185434213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67231212198752292247245617 50423409149064219185434213)
        ·
          refine ⟨9454389215449541097268915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50423409149064219185434213 9454389215449541097268915)
          ·
            refine ⟨14181583823174311645903373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454389215449541097268915 14181583823174311645903373)
            ·
              refine ⟨5318093933690366867213765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14181583823174311645903373 5318093933690366867213765)
              ·
                refine ⟨997142612566943787602581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5318093933690366867213765 997142612566943787602581)
                ·
                  refine ⟨46741059964075490043871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997142612566943787602581 46741059964075490043871)
                  ·
                    rfl

theorem cell23_819251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 6].length) (baseStart_819251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819251 prefixEnd_819251 := by exact prefixLift 819251
  have htrace : WordTrace (prefixWord ++ tailWord_819251) baseStart_819251 baseEnd_819251 := by
    simpa [prefixWord, tailWord_819251, baseEnd_819251] using wordTrace_append hprefix tailTrace_819251
  have hstable : (prefixWord ++ tailWord_819251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819251).length < 2 ^ (prefixWord ++ tailWord_819251).sum := by decide
  have hdescent : baseEnd_819251 < baseStart_819251 := by decide
  rcases family_descends (prefixWord ++ tailWord_819251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819262 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_819262 : Nat := 118140960795 + 819262 * 2 ^ 59
def prefixEnd_819262 : Nat := 4983230072969 + 3 ^ 40 * 819262 * 2
def baseEnd_819262 : Nat := 420675187963878867357289

theorem tailTrace_819262 : CollatzResearch.WordTrace tailWord_819262 prefixEnd_819262 420675187963878867357289 := by
  unfold tailWord_819262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735117494745145956900505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19920626638640778436802693 3735117494745145956900505)
  ·
    refine ⟨2801338121058859467675379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3735117494745145956900505 2801338121058859467675379)
    ·
      refine ⟨4202007181588289201513069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801338121058859467675379 4202007181588289201513069)
      ·
        refine ⟨1575752693095608450567401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4202007181588289201513069 1575752693095608450567401)
        ·
          refine ⟨1181814519821706337925551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575752693095608450567401 1181814519821706337925551)
          ·
            refine ⟨1772721779732559506888327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181814519821706337925551 1772721779732559506888327)
            ·
              refine ⟨2659082669598839260332491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772721779732559506888327 2659082669598839260332491)
              ·
                refine ⟨3988624004398258890498737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659082669598839260332491 3988624004398258890498737)
                ·
                  refine ⟨2991468003298694167874053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988624004398258890498737 2991468003298694167874053)
                  ·
                    refine ⟨560900250618505156476385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991468003298694167874053 560900250618505156476385)
                    ·
                      refine ⟨420675187963878867357289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 560900250618505156476385 420675187963878867357289)
                      ·
                        rfl

theorem cell23_819262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_819262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819262 prefixEnd_819262 := by exact prefixLift 819262
  have htrace : WordTrace (prefixWord ++ tailWord_819262) baseStart_819262 baseEnd_819262 := by
    simpa [prefixWord, tailWord_819262, baseEnd_819262] using wordTrace_append hprefix tailTrace_819262
  have hstable : (prefixWord ++ tailWord_819262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819262).length < 2 ^ (prefixWord ++ tailWord_819262).sum := by decide
  have hdescent : baseEnd_819262 < baseStart_819262 := by decide
  rcases family_descends (prefixWord ++ tailWord_819262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819282 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_819282 : Nat := 118140960795 + 819282 * 2 ^ 59
def prefixEnd_819282 : Nat := 4983230072969 + 3 ^ 40 * 819282 * 2
def baseEnd_819282 : Nat := 420685457576968789107197

theorem tailTrace_819282 : CollatzResearch.WordTrace tailWord_819282 prefixEnd_819282 420685457576968789107197 := by
  unfold tailWord_819282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470417354472177767733025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19921112945259140713954733 7470417354472177767733025)
  ·
    refine ⟨5602813015854133325799769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7470417354472177767733025 5602813015854133325799769)
    ·
      refine ⟨4202109761890599994349827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5602813015854133325799769 4202109761890599994349827)
      ·
        refine ⟨6303164642835899991524741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202109761890599994349827 6303164642835899991524741)
        ·
          refine ⟨1181843370531731248410889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6303164642835899991524741 1181843370531731248410889)
          ·
            refine ⟨886382527898798436308167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181843370531731248410889 886382527898798436308167)
            ·
              refine ⟨1329573791848197654462251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886382527898798436308167 1329573791848197654462251)
              ·
                refine ⟨1994360687772296481693377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329573791848197654462251 1994360687772296481693377)
                ·
                  refine ⟨1495770515829222361270033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994360687772296481693377 1495770515829222361270033)
                  ·
                    refine ⟨1121827886871916770952525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495770515829222361270033 1121827886871916770952525)
                    ·
                      refine ⟨420685457576968789107197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121827886871916770952525 420685457576968789107197)
                      ·
                        rfl

theorem cell23_819282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_819282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819282 prefixEnd_819282 := by exact prefixLift 819282
  have htrace : WordTrace (prefixWord ++ tailWord_819282) baseStart_819282 baseEnd_819282 := by
    simpa [prefixWord, tailWord_819282, baseEnd_819282] using wordTrace_append hprefix tailTrace_819282
  have hstable : (prefixWord ++ tailWord_819282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819282).length < 2 ^ (prefixWord ++ tailWord_819282).sum := by decide
  have hdescent : baseEnd_819282 < baseStart_819282 := by decide
  rcases family_descends (prefixWord ++ tailWord_819282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819312 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 1, 1, 3]
def baseStart_819312 : Nat := 118140960795 + 819312 * 2 ^ 59
def prefixEnd_819312 : Nat := 4983230072969 + 3 ^ 40 * 819312 * 2
def baseEnd_819312 : Nat := 420700861996603671732059

theorem tailTrace_819312 : CollatzResearch.WordTrace tailWord_819312 prefixEnd_819312 420700861996603671732059 := by
  unfold tailWord_819312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941381803890013097262095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19921842405186684129682793 14941381803890013097262095)
  ·
    refine ⟨22412072705835019645893143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14941381803890013097262095 22412072705835019645893143)
    ·
      refine ⟨33618109058752529468839715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22412072705835019645893143 33618109058752529468839715)
      ·
        refine ⟨50427163588128794203259573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33618109058752529468839715 50427163588128794203259573)
        ·
          refine ⟨4727546586387074456555585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50427163588128794203259573 4727546586387074456555585)
          ·
            refine ⟨3545659939790305842416689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727546586387074456555585 3545659939790305842416689)
            ·
              refine ⟨2659244954842729381812517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545659939790305842416689 2659244954842729381812517)
              ·
                refine ⟨498608429033011759089847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2659244954842729381812517 498608429033011759089847)
                ·
                  refine ⟨747912643549517638634771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498608429033011759089847 747912643549517638634771)
                  ·
                    refine ⟨1121868965324276457952157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747912643549517638634771 1121868965324276457952157)
                    ·
                      refine ⟨420700861996603671732059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1121868965324276457952157 420700861996603671732059)
                      ·
                        rfl

theorem cell23_819312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 1, 3].length) (baseStart_819312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819312 prefixEnd_819312 := by exact prefixLift 819312
  have htrace : WordTrace (prefixWord ++ tailWord_819312) baseStart_819312 baseEnd_819312 := by
    simpa [prefixWord, tailWord_819312, baseEnd_819312] using wordTrace_append hprefix tailTrace_819312
  have hstable : (prefixWord ++ tailWord_819312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819312).length < 2 ^ (prefixWord ++ tailWord_819312).sum := by decide
  have hdescent : baseEnd_819312 < baseStart_819312 := by decide
  rcases family_descends (prefixWord ++ tailWord_819312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819391 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_819391 : Nat := 118140960795 + 819391 * 2 ^ 59
def prefixEnd_819391 : Nat := 4983230072969 + 3 ^ 40 * 819391 * 2
def baseEnd_819391 : Nat := 420741426968308862644195

theorem tailTrace_819391 : CollatzResearch.WordTrace tailWord_819391 prefixEnd_819391 420741426968308862644195 := by
  unfold tailWord_819391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885644974493822686650027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19923763316329215124433351 29885644974493822686650027)
  ·
    refine ⟨44828467461740734029975041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885644974493822686650027 44828467461740734029975041)
    ·
      refine ⟨33621350596305550522481281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44828467461740734029975041 33621350596305550522481281)
      ·
        refine ⟨25216012947229162891860961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33621350596305550522481281 25216012947229162891860961)
        ·
          refine ⟨18912009710421872168895721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25216012947229162891860961 18912009710421872168895721)
          ·
            refine ⟨14184007282816404126671791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18912009710421872168895721 14184007282816404126671791)
            ·
              refine ⟨21276010924224606190007687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14184007282816404126671791 21276010924224606190007687)
              ·
                refine ⟨31914016386336909285011531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21276010924224606190007687 31914016386336909285011531)
                ·
                  refine ⟨47871024579505363927517297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31914016386336909285011531 47871024579505363927517297)
                  ·
                    refine ⟨35903268434629022945637973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47871024579505363927517297 35903268434629022945637973)
                    ·
                      refine ⟨420741426968308862644195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 35903268434629022945637973 420741426968308862644195)
                      ·
                        rfl

theorem cell23_819391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_819391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819391 prefixEnd_819391 := by exact prefixLift 819391
  have htrace : WordTrace (prefixWord ++ tailWord_819391) baseStart_819391 baseEnd_819391 := by
    simpa [prefixWord, tailWord_819391, baseEnd_819391] using wordTrace_append hprefix tailTrace_819391
  have hstable : (prefixWord ++ tailWord_819391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819391).length < 2 ^ (prefixWord ++ tailWord_819391).sum := by decide
  have hdescent : baseEnd_819391 < baseStart_819391 := by decide
  rcases family_descends (prefixWord ++ tailWord_819391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_819401 : Nat := 118140960795 + 819401 * 2 ^ 59
def prefixEnd_819401 : Nat := 4983230072969 + 3 ^ 40 * 819401 * 2
def baseEnd_819401 : Nat := 140248853924951274506383

theorem tailTrace_819401 : CollatzResearch.WordTrace tailWord_819401 prefixEnd_819401 140248853924951274506383 := by
  unfold tailWord_819401
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886009704457594394514057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19924006469638396263009371 29886009704457594394514057)
  ·
    refine ⟨22414507278343195795885543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29886009704457594394514057 22414507278343195795885543)
    ·
      refine ⟨33621760917514793693828315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22414507278343195795885543 33621760917514793693828315)
      ·
        refine ⟨50432641376272190540742473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33621760917514793693828315 50432641376272190540742473)
        ·
          refine ⟨37824481032204142905556855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50432641376272190540742473 37824481032204142905556855)
          ·
            refine ⟨56736721548306214358335283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37824481032204142905556855 56736721548306214358335283)
            ·
              refine ⟨85105082322459321537502925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56736721548306214358335283 85105082322459321537502925)
              ·
                refine ⟨31914405870922245576563597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85105082322459321537502925 31914405870922245576563597)
                ·
                  refine ⟨11967902201595842091211349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31914405870922245576563597 11967902201595842091211349)
                  ·
                    refine ⟨140248853924951274506383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11967902201595842091211349 140248853924951274506383)
                    ·
                      rfl

theorem cell23_819401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_819401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819401 prefixEnd_819401 := by exact prefixLift 819401
  have htrace : WordTrace (prefixWord ++ tailWord_819401) baseStart_819401 baseEnd_819401 := by
    simpa [prefixWord, tailWord_819401, baseEnd_819401] using wordTrace_append hprefix tailTrace_819401
  have hstable : (prefixWord ++ tailWord_819401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819401).length < 2 ^ (prefixWord ++ tailWord_819401).sum := by decide
  have hdescent : baseEnd_819401 < baseStart_819401 := by decide
  rcases family_descends (prefixWord ++ tailWord_819401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819425 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_819425 : Nat := 118140960795 + 819425 * 2 ^ 59
def prefixEnd_819425 : Nat := 4983230072969 + 3 ^ 40 * 819425 * 2
def baseEnd_819425 : Nat := 420758885310561729619039

theorem tailTrace_819425 : CollatzResearch.WordTrace tailWord_819425 prefixEnd_819425 420758885310561729619039 := by
  unfold tailWord_819425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886885056370646493387729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19924590037580430995591819 29886885056370646493387729)
  ·
    refine ⟨22415163792277984870040797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29886885056370646493387729 22415163792277984870040797)
    ·
      refine ⟨8405686422104244326265299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22415163792277984870040797 8405686422104244326265299)
      ·
        refine ⟨12608529633156366489397949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405686422104244326265299 12608529633156366489397949)
        ·
          refine ⟨4728198612433637433524231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12608529633156366489397949 4728198612433637433524231)
          ·
            refine ⟨7092297918650456150286347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728198612433637433524231 7092297918650456150286347)
            ·
              refine ⟨10638446877975684225429521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092297918650456150286347 10638446877975684225429521)
              ·
                refine ⟨7978835158481763169072141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10638446877975684225429521 7978835158481763169072141)
                ·
                  refine ⟨2992063184430661188402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7978835158481763169072141 2992063184430661188402053)
                  ·
                    refine ⟨561011847080748972825385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992063184430661188402053 561011847080748972825385)
                    ·
                      refine ⟨420758885310561729619039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561011847080748972825385 420758885310561729619039)
                      ·
                        rfl

theorem cell23_819425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_819425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819425 prefixEnd_819425 := by exact prefixLift 819425
  have htrace : WordTrace (prefixWord ++ tailWord_819425) baseStart_819425 baseEnd_819425 := by
    simpa [prefixWord, tailWord_819425, baseEnd_819425] using wordTrace_append hprefix tailTrace_819425
  have hstable : (prefixWord ++ tailWord_819425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819425).length < 2 ^ (prefixWord ++ tailWord_819425).sum := by decide
  have hdescent : baseEnd_819425 < baseStart_819425 := by decide
  rcases family_descends (prefixWord ++ tailWord_819425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819426 : List Nat := [3, 3, 4, 1, 2, 1, 1, 8]
def baseStart_819426 : Nat := 118140960795 + 819426 * 2 ^ 59
def prefixEnd_819426 : Nat := 4983230072969 + 3 ^ 40 * 819426 * 2
def baseEnd_819426 : Nat := 15583681436711712063205

theorem tailTrace_819426 : CollatzResearch.WordTrace tailWord_819426 prefixEnd_819426 15583681436711712063205 := by
  unfold tailWord_819426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471730382341755916043533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19924614352911349109449421 7471730382341755916043533)
  ·
    refine ⟨2801898893378158468516325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7471730382341755916043533 2801898893378158468516325)
    ·
      refine ⟨525356042508404712846811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2801898893378158468516325 525356042508404712846811)
      ·
        refine ⟨788034063762607069270217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525356042508404712846811 788034063762607069270217)
        ·
          refine ⟨591025547821955301952663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788034063762607069270217 591025547821955301952663)
          ·
            refine ⟨886538321732932952928995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591025547821955301952663 886538321732932952928995)
            ·
              refine ⟨1329807482599399429393493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886538321732932952928995 1329807482599399429393493)
              ·
                refine ⟨15583681436711712063205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1329807482599399429393493 15583681436711712063205)
                ·
                  rfl

theorem cell23_819426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_819426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819426 prefixEnd_819426 := by exact prefixLift 819426
  have htrace : WordTrace (prefixWord ++ tailWord_819426) baseStart_819426 baseEnd_819426 := by
    simpa [prefixWord, tailWord_819426, baseEnd_819426] using wordTrace_append hprefix tailTrace_819426
  have hstable : (prefixWord ++ tailWord_819426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819426).length < 2 ^ (prefixWord ++ tailWord_819426).sum := by decide
  have hdescent : baseEnd_819426 < baseStart_819426 := by decide
  rcases family_descends (prefixWord ++ tailWord_819426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819442 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_819442 : Nat := 118140960795 + 819442 * 2 ^ 59
def prefixEnd_819442 : Nat := 4983230072969 + 3 ^ 40 * 819442 * 2
def baseEnd_819442 : Nat := 420767614481688163106461

theorem tailTrace_819442 : CollatzResearch.WordTrace tailWord_819442 prefixEnd_819442 420767614481688163106461 := by
  unfold tailWord_819442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471876274327264599189145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19925003398206038931171053 7471876274327264599189145)
  ·
    refine ⟨5603907205745448449391859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7471876274327264599189145 5603907205745448449391859)
    ·
      refine ⟨8405860808618172674087789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5603907205745448449391859 8405860808618172674087789)
      ·
        refine ⟨3152197803231814752782921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8405860808618172674087789 3152197803231814752782921)
        ·
          refine ⟨2364148352423861064587191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152197803231814752782921 2364148352423861064587191)
          ·
            refine ⟨3546222528635791596880787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364148352423861064587191 3546222528635791596880787)
            ·
              refine ⟨5319333792953687395321181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546222528635791596880787 5319333792953687395321181)
              ·
                refine ⟨1994750172357632773245443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5319333792953687395321181 1994750172357632773245443)
                ·
                  refine ⟨2992125258536449159868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994750172357632773245443 2992125258536449159868165)
                  ·
                    refine ⟨561023485975584217475281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992125258536449159868165 561023485975584217475281)
                    ·
                      refine ⟨420767614481688163106461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561023485975584217475281 420767614481688163106461)
                      ·
                        rfl

theorem cell23_819442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_819442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819442 prefixEnd_819442 := by exact prefixLift 819442
  have htrace : WordTrace (prefixWord ++ tailWord_819442) baseStart_819442 baseEnd_819442 := by
    simpa [prefixWord, tailWord_819442, baseEnd_819442] using wordTrace_append hprefix tailTrace_819442
  have hstable : (prefixWord ++ tailWord_819442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819442).length < 2 ^ (prefixWord ++ tailWord_819442).sum := by decide
  have hdescent : baseEnd_819442 < baseStart_819442 := by decide
  rcases family_descends (prefixWord ++ tailWord_819442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819463 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_819463 : Nat := 118140960795 + 819463 * 2 ^ 59
def prefixEnd_819463 : Nat := 4983230072969 + 3 ^ 40 * 819463 * 2
def baseEnd_819463 : Nat := 420778397575432580943865

theorem tailTrace_819463 : CollatzResearch.WordTrace tailWord_819463 prefixEnd_819463 420778397575432580943865 := by
  unfold tailWord_819463
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888271030232978983271043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19925514020155319322180695 29888271030232978983271043)
  ·
    refine ⟨44832406545349468474906565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29888271030232978983271043 44832406545349468474906565)
    ·
      refine ⟨8406076227253025339044981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44832406545349468474906565 8406076227253025339044981)
      ·
        refine ⟨788069646304971125535467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8406076227253025339044981 788069646304971125535467)
        ·
          refine ⟨1182104469457456688303201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788069646304971125535467 1182104469457456688303201)
          ·
            refine ⟨886578352093092516227401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182104469457456688303201 886578352093092516227401)
            ·
              refine ⟨664933764069819387170551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886578352093092516227401 664933764069819387170551)
              ·
                refine ⟨997400646104729080755827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664933764069819387170551 997400646104729080755827)
                ·
                  refine ⟨1496100969157093621133741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997400646104729080755827 1496100969157093621133741)
                  ·
                    refine ⟨561037863433910107925153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496100969157093621133741 561037863433910107925153)
                    ·
                      refine ⟨420778397575432580943865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561037863433910107925153 420778397575432580943865)
                      ·
                        rfl

theorem cell23_819463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_819463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819463 prefixEnd_819463 := by exact prefixLift 819463
  have htrace : WordTrace (prefixWord ++ tailWord_819463) baseStart_819463 baseEnd_819463 := by
    simpa [prefixWord, tailWord_819463, baseEnd_819463] using wordTrace_append hprefix tailTrace_819463
  have hstable : (prefixWord ++ tailWord_819463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819463).length < 2 ^ (prefixWord ++ tailWord_819463).sum := by decide
  have hdescent : baseEnd_819463 < baseStart_819463 := by decide
  rcases family_descends (prefixWord ++ tailWord_819463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819465 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 5]
def baseStart_819465 : Nat := 118140960795 + 819465 * 2 ^ 59
def prefixEnd_819465 : Nat := 4983230072969 + 3 ^ 40 * 819465 * 2
def baseEnd_819465 : Nat := 46753269392971285902095

theorem tailTrace_819465 : CollatzResearch.WordTrace tailWord_819465 prefixEnd_819465 46753269392971285902095 := by
  unfold tailWord_819465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888343976225733324843849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19925562650817155549895899 29888343976225733324843849)
  ·
    refine ⟨22416257982169299993632887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29888343976225733324843849 22416257982169299993632887)
    ·
      refine ⟨33624386973253949990449331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22416257982169299993632887 33624386973253949990449331)
      ·
        refine ⟨50436580459880924985673997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33624386973253949990449331 50436580459880924985673997)
        ·
          refine ⟨18913717672455346869627749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50436580459880924985673997 18913717672455346869627749)
          ·
            refine ⟨3546322063585377538055203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18913717672455346869627749 3546322063585377538055203)
            ·
              refine ⟨5319483095378066307082805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546322063585377538055203 5319483095378066307082805)
              ·
                refine ⟨498701540191693716289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5319483095378066307082805 498701540191693716289013)
                ·
                  refine ⟨46753269392971285902095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498701540191693716289013 46753269392971285902095)
                  ·
                    rfl

theorem cell23_819465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 5].length) (baseStart_819465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819465 prefixEnd_819465 := by exact prefixLift 819465
  have htrace : WordTrace (prefixWord ++ tailWord_819465) baseStart_819465 baseEnd_819465 := by
    simpa [prefixWord, tailWord_819465, baseEnd_819465] using wordTrace_append hprefix tailTrace_819465
  have hstable : (prefixWord ++ tailWord_819465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819465).length < 2 ^ (prefixWord ++ tailWord_819465).sum := by decide
  have hdescent : baseEnd_819465 < baseStart_819465 := by decide
  rcases family_descends (prefixWord ++ tailWord_819465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819528 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_819528 : Nat := 118140960795 + 819528 * 2 ^ 59
def prefixEnd_819528 : Nat := 4983230072969 + 3 ^ 40 * 819528 * 2
def baseEnd_819528 : Nat := 420811773817974826631065

theorem tailTrace_819528 : CollatzResearch.WordTrace tailWord_819528 prefixEnd_819528 420811773817974826631065 := by
  unfold tailWord_819528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945320887498747542193619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19927094516664996722924825 14945320887498747542193619)
  ·
    refine ⟨22417981331248121313290429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14945320887498747542193619 22417981331248121313290429)
    ·
      refine ⟨8406742999218045492483911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22417981331248121313290429 8406742999218045492483911)
      ·
        refine ⟨12610114498827068238725867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8406742999218045492483911 12610114498827068238725867)
        ·
          refine ⟨18915171748240602358088801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12610114498827068238725867 18915171748240602358088801)
          ·
            refine ⟨14186378811180451768566601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18915171748240602358088801 14186378811180451768566601)
            ·
              refine ⟨10639784108385338826424951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14186378811180451768566601 10639784108385338826424951)
              ·
                refine ⟨15959676162578008239637427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10639784108385338826424951 15959676162578008239637427)
                ·
                  refine ⟨23939514243867012359456141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15959676162578008239637427 23939514243867012359456141)
                  ·
                    refine ⟨8977317841450129634796053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23939514243867012359456141 8977317841450129634796053)
                    ·
                      refine ⟨420811773817974826631065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8977317841450129634796053 420811773817974826631065)
                      ·
                        rfl

theorem cell23_819528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_819528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819528 prefixEnd_819528 := by exact prefixLift 819528
  have htrace : WordTrace (prefixWord ++ tailWord_819528) baseStart_819528 baseEnd_819528 := by
    simpa [prefixWord, tailWord_819528, baseEnd_819528] using wordTrace_append hprefix tailTrace_819528
  have hstable : (prefixWord ++ tailWord_819528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819528).length < 2 ^ (prefixWord ++ tailWord_819528).sum := by decide
  have hdescent : baseEnd_819528 < baseStart_819528 := by decide
  rcases family_descends (prefixWord ++ tailWord_819528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819555 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 6]
def baseStart_819555 : Nat := 118140960795 + 819555 * 2 ^ 59
def prefixEnd_819555 : Nat := 4983230072969 + 3 ^ 40 * 819555 * 2
def baseEnd_819555 : Nat := 46758404199516246777049

theorem tailTrace_819555 : CollatzResearch.WordTrace tailWord_819555 prefixEnd_819555 46758404199516246777049 := by
  unfold tailWord_819555
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891626545899678695620119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19927751030599785797080079 29891626545899678695620119)
  ·
    refine ⟨44837439818849518043430179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29891626545899678695620119 44837439818849518043430179)
    ·
      refine ⟨67256159728274277065145269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44837439818849518043430179 67256159728274277065145269)
      ·
        refine ⟨6305264974525713474857369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67256159728274277065145269 6305264974525713474857369)
        ·
          refine ⟨4728948730894285106143027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6305264974525713474857369 4728948730894285106143027)
          ·
            refine ⟨7093423096341427659214541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728948730894285106143027 7093423096341427659214541)
            ·
              refine ⟨2660033661128035372205453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7093423096341427659214541 2660033661128035372205453)
              ·
                refine ⟨997512622923013264577045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2660033661128035372205453 997512622923013264577045)
                ·
                  refine ⟨46758404199516246777049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997512622923013264577045 46758404199516246777049)
                  ·
                    rfl

theorem cell23_819555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 6].length) (baseStart_819555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819555 prefixEnd_819555 := by exact prefixLift 819555
  have htrace : WordTrace (prefixWord ++ tailWord_819555) baseStart_819555 baseEnd_819555 := by
    simpa [prefixWord, tailWord_819555, baseEnd_819555] using wordTrace_append hprefix tailTrace_819555
  have hstable : (prefixWord ++ tailWord_819555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819555).length < 2 ^ (prefixWord ++ tailWord_819555).sum := by decide
  have hdescent : baseEnd_819555 < baseStart_819555 := by decide
  rcases family_descends (prefixWord ++ tailWord_819555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819639 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_819639 : Nat := 118140960795 + 819639 * 2 ^ 59
def prefixEnd_819639 : Nat := 4983230072969 + 3 ^ 40 * 819639 * 2
def baseEnd_819639 : Nat := 420868770170623892343055

theorem tailTrace_819639 : CollatzResearch.WordTrace tailWord_819639 prefixEnd_819639 420868770170623892343055 := by
  unfold tailWord_819639
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894690277595361041677971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19929793518396907361118647 29894690277595361041677971)
  ·
    refine ⟨44842035416393041562516957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29894690277595361041677971 44842035416393041562516957)
    ·
      refine ⟨16815763281147390585943859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44842035416393041562516957 16815763281147390585943859)
      ·
        refine ⟨25223644921721085878915789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815763281147390585943859 25223644921721085878915789)
        ·
          refine ⟨9458866845645407204593421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25223644921721085878915789 9458866845645407204593421)
          ·
            refine ⟨3547075067117027701722533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9458866845645407204593421 3547075067117027701722533)
            ·
              refine ⟨665076575084442694072975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3547075067117027701722533 665076575084442694072975)
              ·
                refine ⟨997614862626664041109463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665076575084442694072975 997614862626664041109463)
                ·
                  refine ⟨1496422293939996061664195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997614862626664041109463 1496422293939996061664195)
                  ·
                    refine ⟨2244633440909994092496293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1496422293939996061664195 2244633440909994092496293)
                    ·
                      refine ⟨420868770170623892343055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2244633440909994092496293 420868770170623892343055)
                      ·
                        rfl

theorem cell23_819639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_819639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819639 prefixEnd_819639 := by exact prefixLift 819639
  have htrace : WordTrace (prefixWord ++ tailWord_819639) baseStart_819639 baseEnd_819639 := by
    simpa [prefixWord, tailWord_819639, baseEnd_819639] using wordTrace_append hprefix tailTrace_819639
  have hstable : (prefixWord ++ tailWord_819639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819639).length < 2 ^ (prefixWord ++ tailWord_819639).sum := by decide
  have hdescent : baseEnd_819639 < baseStart_819639 := by decide
  rcases family_descends (prefixWord ++ tailWord_819639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819645 : List Nat := [1, 4, 1, 2, 2, 3, 10]
def baseStart_819645 : Nat := 118140960795 + 819645 * 2 ^ 59
def prefixEnd_819645 : Nat := 4983230072969 + 3 ^ 40 * 819645 * 2
def baseEnd_819645 : Nat := 5195948778451245294667

theorem tailTrace_819645 : CollatzResearch.WordTrace tailWord_819645 prefixEnd_819645 5195948778451245294667 := by
  unfold tailWord_819645
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894909115573624066396389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19929939410382416044264259 29894909115573624066396389)
  ·
    refine ⟨5605295459170054512449323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29894909115573624066396389 5605295459170054512449323)
    ·
      refine ⟨8407943188755081768673985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605295459170054512449323 8407943188755081768673985)
      ·
        refine ⟨6305957391566311326505489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8407943188755081768673985 6305957391566311326505489)
        ·
          refine ⟨4729468043674733494879117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6305957391566311326505489 4729468043674733494879117)
          ·
            refine ⟨1773550516378025060579669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4729468043674733494879117 1773550516378025060579669)
            ·
              refine ⟨5195948778451245294667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1773550516378025060579669 5195948778451245294667)
              ·
                rfl

theorem cell23_819645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 10].length) (baseStart_819645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819645 prefixEnd_819645 := by exact prefixLift 819645
  have htrace : WordTrace (prefixWord ++ tailWord_819645) baseStart_819645 baseEnd_819645 := by
    simpa [prefixWord, tailWord_819645, baseEnd_819645] using wordTrace_append hprefix tailTrace_819645
  have hstable : (prefixWord ++ tailWord_819645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819645).length < 2 ^ (prefixWord ++ tailWord_819645).sum := by decide
  have hdescent : baseEnd_819645 < baseStart_819645 := by decide
  rcases family_descends (prefixWord ++ tailWord_819645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819656 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_819656 : Nat := 118140960795 + 819656 * 2 ^ 59
def prefixEnd_819656 : Nat := 4983230072969 + 3 ^ 40 * 819656 * 2
def baseEnd_819656 : Nat := 420877499341750325830477

theorem tailTrace_819656 : CollatzResearch.WordTrace tailWord_819656 prefixEnd_819656 420877499341750325830477 := by
  unfold tailWord_819656
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947655159266886472523411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19930206879022515296697881 14947655159266886472523411)
  ·
    refine ⟨22421482738900329708785117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947655159266886472523411 22421482738900329708785117)
    ·
      refine ⟨8408056027087623640794419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22421482738900329708785117 8408056027087623640794419)
      ·
        refine ⟨12612084040631435461191629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408056027087623640794419 12612084040631435461191629)
        ·
          refine ⟨4729531515236788297946861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12612084040631435461191629 4729531515236788297946861)
          ·
            refine ⟨1773574318213795611730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4729531515236788297946861 1773574318213795611730073)
            ·
              refine ⟨1330180738660346708797555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773574318213795611730073 1330180738660346708797555)
              ·
                refine ⟨1995271107990520063196333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330180738660346708797555 1995271107990520063196333)
                ·
                  refine ⟨748226665496445023698625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1995271107990520063196333 748226665496445023698625)
                  ·
                    refine ⟨561169999122333767773969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748226665496445023698625 561169999122333767773969)
                    ·
                      refine ⟨420877499341750325830477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561169999122333767773969 420877499341750325830477)
                      ·
                        rfl

theorem cell23_819656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_819656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819656 prefixEnd_819656 := by exact prefixLift 819656
  have htrace : WordTrace (prefixWord ++ tailWord_819656) baseStart_819656 baseEnd_819656 := by
    simpa [prefixWord, tailWord_819656, baseEnd_819656] using wordTrace_append hprefix tailTrace_819656
  have hstable : (prefixWord ++ tailWord_819656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819656).length < 2 ^ (prefixWord ++ tailWord_819656).sum := by decide
  have hdescent : baseEnd_819656 < baseStart_819656 := by decide
  rcases family_descends (prefixWord ++ tailWord_819656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819666 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_819666 : Nat := 118140960795 + 819666 * 2 ^ 59
def prefixEnd_819666 : Nat := 4983230072969 + 3 ^ 40 * 819666 * 2
def baseEnd_819666 : Nat := 140294211382765095568477

theorem tailTrace_819666 : CollatzResearch.WordTrace tailWord_819666 prefixEnd_819666 140294211382765095568477 := by
  unfold tailWord_819666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473918762124386163227713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19930450032331696435273901 7473918762124386163227713)
  ·
    refine ⟨5605439071593289622420785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7473918762124386163227713 5605439071593289622420785)
    ·
      refine ⟨4204079303694967216815589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605439071593289622420785 4204079303694967216815589)
      ·
        refine ⟨788264869442806353152923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4204079303694967216815589 788264869442806353152923)
        ·
          refine ⟨1182397304164209529729385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788264869442806353152923 1182397304164209529729385)
          ·
            refine ⟨886797978123157147297039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182397304164209529729385 886797978123157147297039)
            ·
              refine ⟨1330196967184735720945559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886797978123157147297039 1330196967184735720945559)
              ·
                refine ⟨1995295450777103581418339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330196967184735720945559 1995295450777103581418339)
                ·
                  refine ⟨2992943176165655372127509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995295450777103581418339 2992943176165655372127509)
                  ·
                    refine ⟨140294211382765095568477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2992943176165655372127509 140294211382765095568477)
                    ·
                      rfl

theorem cell23_819666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_819666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819666 prefixEnd_819666 := by exact prefixLift 819666
  have htrace : WordTrace (prefixWord ++ tailWord_819666) baseStart_819666 baseEnd_819666 := by
    simpa [prefixWord, tailWord_819666, baseEnd_819666] using wordTrace_append hprefix tailTrace_819666
  have hstable : (prefixWord ++ tailWord_819666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819666).length < 2 ^ (prefixWord ++ tailWord_819666).sum := by decide
  have hdescent : baseEnd_819666 < baseStart_819666 := by decide
  rcases family_descends (prefixWord ++ tailWord_819666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819669 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_819669 : Nat := 118140960795 + 819669 * 2 ^ 59
def prefixEnd_819669 : Nat := 4983230072969 + 3 ^ 40 * 819669 * 2
def baseEnd_819669 : Nat := 420884174590258774967917

theorem tailTrace_819669 : CollatzResearch.WordTrace tailWord_819669 prefixEnd_819669 420884174590258774967917 := by
  unfold tailWord_819669
  simp only [CollatzResearch.WordTrace]
  refine ⟨29895784467486676165270061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19930522978324450776846707 29895784467486676165270061)
  ·
    refine ⟨11210919175307503561976273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29895784467486676165270061 11210919175307503561976273)
    ·
      refine ⟨8408189381480627671482205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11210919175307503561976273 8408189381480627671482205)
      ·
        refine ⟨3153071018055235376805827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8408189381480627671482205 3153071018055235376805827)
        ·
          refine ⟨4729606527082853065208741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153071018055235376805827 4729606527082853065208741)
          ·
            refine ⟨886801223828034949726639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4729606527082853065208741 886801223828034949726639)
            ·
              refine ⟨1330201835742052424589959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886801223828034949726639 1330201835742052424589959)
              ·
                refine ⟨1995302753613078636884939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330201835742052424589959 1995302753613078636884939)
                ·
                  refine ⟨2992954130419617955327409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995302753613078636884939 2992954130419617955327409)
                  ·
                    refine ⟨2244715597814713466495557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2992954130419617955327409 2244715597814713466495557)
                    ·
                      refine ⟨420884174590258774967917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2244715597814713466495557 420884174590258774967917)
                      ·
                        rfl

theorem cell23_819669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_819669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819669 prefixEnd_819669 := by exact prefixLift 819669
  have htrace : WordTrace (prefixWord ++ tailWord_819669) baseStart_819669 baseEnd_819669 := by
    simpa [prefixWord, tailWord_819669, baseEnd_819669] using wordTrace_append hprefix tailTrace_819669
  have hstable : (prefixWord ++ tailWord_819669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819669).length < 2 ^ (prefixWord ++ tailWord_819669).sum := by decide
  have hdescent : baseEnd_819669 < baseStart_819669 := by decide
  rcases family_descends (prefixWord ++ tailWord_819669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819690 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_819690 : Nat := 118140960795 + 819690 * 2 ^ 59
def prefixEnd_819690 : Nat := 4983230072969 + 3 ^ 40 * 819690 * 2
def baseEnd_819690 : Nat := 420894957684003192805321

theorem tailTrace_819690 : CollatzResearch.WordTrace tailWord_819690 prefixEnd_819690 420894957684003192805321 := by
  unfold tailWord_819690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474137600102649187946131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19931033600273731167856349 7474137600102649187946131)
  ·
    refine ⟨11211206400153973781919197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7474137600102649187946131 11211206400153973781919197)
    ·
      refine ⟨4204202400057740168219699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11211206400153973781919197 4204202400057740168219699)
      ·
        refine ⟨6306303600086610252329549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204202400057740168219699 6306303600086610252329549)
        ·
          refine ⟨2364863850032478844623581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6306303600086610252329549 2364863850032478844623581)
          ·
            refine ⟨886823943762179566733843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2364863850032478844623581 886823943762179566733843)
            ·
              refine ⟨1330235915643269350100765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886823943762179566733843 1330235915643269350100765)
              ·
                refine ⟨498838468366226006287787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330235915643269350100765 498838468366226006287787)
                ·
                  refine ⟨748257702549339009431681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498838468366226006287787 748257702549339009431681)
                  ·
                    refine ⟨561193276912004257073761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748257702549339009431681 561193276912004257073761)
                    ·
                      refine ⟨420894957684003192805321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561193276912004257073761 420894957684003192805321)
                      ·
                        rfl

theorem cell23_819690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_819690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819690 prefixEnd_819690 := by exact prefixLift 819690
  have htrace : WordTrace (prefixWord ++ tailWord_819690) baseStart_819690 baseEnd_819690 := by
    simpa [prefixWord, tailWord_819690, baseEnd_819690] using wordTrace_append hprefix tailTrace_819690
  have hstable : (prefixWord ++ tailWord_819690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819690).length < 2 ^ (prefixWord ++ tailWord_819690).sum := by decide
  have hdescent : baseEnd_819690 < baseStart_819690 := by decide
  rcases family_descends (prefixWord ++ tailWord_819690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819695 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_819695 : Nat := 118140960795 + 819695 * 2 ^ 59
def prefixEnd_819695 : Nat := 4983230072969 + 3 ^ 40 * 819695 * 2
def baseEnd_819695 : Nat := 420897525087275673242797

theorem tailTrace_819695 : CollatzResearch.WordTrace tailWord_819695 prefixEnd_819695 420897525087275673242797 := by
  unfold tailWord_819695
  simp only [CollatzResearch.WordTrace]
  refine ⟨29896732765392482605716539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931155176928321737144359 29896732765392482605716539)
  ·
    refine ⟨44845099148088723908574809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29896732765392482605716539 44845099148088723908574809)
    ·
      refine ⟨33633824361066542931431107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44845099148088723908574809 33633824361066542931431107)
      ·
        refine ⟨50450736541599814397146661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33633824361066542931431107 50450736541599814397146661)
        ·
          refine ⟨9459513101549965199464999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50450736541599814397146661 9459513101549965199464999)
          ·
            refine ⟨14189269652324947799197499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9459513101549965199464999 14189269652324947799197499)
            ·
              refine ⟨21283904478487421698796249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14189269652324947799197499 21283904478487421698796249)
              ·
                refine ⟨15962928358865566274097187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21283904478487421698796249 15962928358865566274097187)
                ·
                  refine ⟨23944392538298349411145781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15962928358865566274097187 23944392538298349411145781)
                  ·
                    refine ⟨2244786800465470257294917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23944392538298349411145781 2244786800465470257294917)
                    ·
                      refine ⟨420897525087275673242797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2244786800465470257294917 420897525087275673242797)
                      ·
                        rfl

theorem cell23_819695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_819695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819695 prefixEnd_819695 := by exact prefixLift 819695
  have htrace : WordTrace (prefixWord ++ tailWord_819695) baseStart_819695 baseEnd_819695 := by
    simpa [prefixWord, tailWord_819695, baseEnd_819695] using wordTrace_append hprefix tailTrace_819695
  have hstable : (prefixWord ++ tailWord_819695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819695).length < 2 ^ (prefixWord ++ tailWord_819695).sum := by decide
  have hdescent : baseEnd_819695 < baseStart_819695 := by decide
  rcases family_descends (prefixWord ++ tailWord_819695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819699 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 1, 3, 2]
def baseStart_819699 : Nat := 118140960795 + 819699 * 2 ^ 59
def prefixEnd_819699 : Nat := 4983230072969 + 3 ^ 40 * 819699 * 2
def baseEnd_819699 : Nat := 420899579009893657592779

theorem tailTrace_819699 : CollatzResearch.WordTrace tailWord_819699 prefixEnd_819699 420899579009893657592779 := by
  unfold tailWord_819699
  simp only [CollatzResearch.WordTrace]
  refine ⟨29896878657377991288862151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931252438251994192574767 29896878657377991288862151)
  ·
    refine ⟨44845317986066986933293227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29896878657377991288862151 44845317986066986933293227)
    ·
      refine ⟨67267976979100480399939841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44845317986066986933293227 67267976979100480399939841)
      ·
        refine ⟨50450982734325360299954881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67267976979100480399939841 50450982734325360299954881)
        ·
          refine ⟨37838237050744020224966161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50450982734325360299954881 37838237050744020224966161)
          ·
            refine ⟨28378677788058015168724621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37838237050744020224966161 28378677788058015168724621)
            ·
              refine ⟨10642004170521755688271733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28378677788058015168724621 10642004170521755688271733)
              ·
                refine ⟨997687890986414595775475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10642004170521755688271733 997687890986414595775475)
                ·
                  refine ⟨1496531836479621893663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997687890986414595775475 1496531836479621893663213)
                  ·
                    refine ⟨561199438679858210123705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496531836479621893663213 561199438679858210123705)
                    ·
                      refine ⟨420899579009893657592779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561199438679858210123705 420899579009893657592779)
                      ·
                        rfl

theorem cell23_819699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3, 2].length) (baseStart_819699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819699 prefixEnd_819699 := by exact prefixLift 819699
  have htrace : WordTrace (prefixWord ++ tailWord_819699) baseStart_819699 baseEnd_819699 := by
    simpa [prefixWord, tailWord_819699, baseEnd_819699] using wordTrace_append hprefix tailTrace_819699
  have hstable : (prefixWord ++ tailWord_819699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819699).length < 2 ^ (prefixWord ++ tailWord_819699).sum := by decide
  have hdescent : baseEnd_819699 < baseStart_819699 := by decide
  rcases family_descends (prefixWord ++ tailWord_819699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819702 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_819702 : Nat := 118140960795 + 819702 * 2 ^ 59
def prefixEnd_819702 : Nat := 4983230072969 + 3 ^ 40 * 819702 * 2
def baseEnd_819702 : Nat := 420901119451857145855265

theorem tailTrace_819702 : CollatzResearch.WordTrace tailWord_819702 prefixEnd_819702 420901119451857145855265 := by
  unfold tailWord_819702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868561754772945175076335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19931325384244748534147573 1868561754772945175076335)
  ·
    refine ⟨2802842632159417762614503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868561754772945175076335 2802842632159417762614503)
    ·
      refine ⟨4204263948239126643921755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802842632159417762614503 4204263948239126643921755)
      ·
        refine ⟨6306395922358689965882633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204263948239126643921755 6306395922358689965882633)
        ·
          refine ⟨4729796941769017474411975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6306395922358689965882633 4729796941769017474411975)
          ·
            refine ⟨7094695412653526211617963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729796941769017474411975 7094695412653526211617963)
            ·
              refine ⟨10642043118980289317426945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094695412653526211617963 10642043118980289317426945)
              ·
                refine ⟨7981532339235216988070209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642043118980289317426945 7981532339235216988070209)
                ·
                  refine ⟨5986149254426412741052657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981532339235216988070209 5986149254426412741052657)
                  ·
                    refine ⟨4489611940819809555789493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5986149254426412741052657 4489611940819809555789493)
                    ·
                      refine ⟨420901119451857145855265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4489611940819809555789493 420901119451857145855265)
                      ·
                        rfl

theorem cell23_819702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_819702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819702 prefixEnd_819702 := by exact prefixLift 819702
  have htrace : WordTrace (prefixWord ++ tailWord_819702) baseStart_819702 baseEnd_819702 := by
    simpa [prefixWord, tailWord_819702, baseEnd_819702] using wordTrace_append hprefix tailTrace_819702
  have hstable : (prefixWord ++ tailWord_819702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819702).length < 2 ^ (prefixWord ++ tailWord_819702).sum := by decide
  have hdescent : baseEnd_819702 < baseStart_819702 := by decide
  rcases family_descends (prefixWord ++ tailWord_819702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819705 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_819705 : Nat := 118140960795 + 819705 * 2 ^ 59
def prefixEnd_819705 : Nat := 4983230072969 + 3 ^ 40 * 819705 * 2
def baseEnd_819705 : Nat := 140300886631273544705917

theorem tailTrace_819705 : CollatzResearch.WordTrace tailWord_819705 prefixEnd_819705 140300886631273544705917 := by
  unfold tailWord_819705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897097495356254313580569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931398330237502875720379 29897097495356254313580569)
  ·
    refine ⟨22422823121517190735185427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29897097495356254313580569 22422823121517190735185427)
    ·
      refine ⟨33634234682275786102778141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22422823121517190735185427 33634234682275786102778141)
      ·
        refine ⟨12612838005853419788541803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33634234682275786102778141 12612838005853419788541803)
        ·
          refine ⟨18919257008780129682812705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612838005853419788541803 18919257008780129682812705)
          ·
            refine ⟨14189442756585097262109529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18919257008780129682812705 14189442756585097262109529)
            ·
              refine ⟨10642082067438822946582147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14189442756585097262109529 10642082067438822946582147)
              ·
                refine ⟨15963123101158234419873221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10642082067438822946582147 15963123101158234419873221)
                ·
                  refine ⟨2993085581467168953726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15963123101158234419873221 2993085581467168953726229)
                  ·
                    refine ⟨140300886631273544705917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2993085581467168953726229 140300886631273544705917)
                    ·
                      rfl

theorem cell23_819705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_819705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819705 prefixEnd_819705 := by exact prefixLift 819705
  have htrace : WordTrace (prefixWord ++ tailWord_819705) baseStart_819705 baseEnd_819705 := by
    simpa [prefixWord, tailWord_819705, baseEnd_819705] using wordTrace_append hprefix tailTrace_819705
  have hstable : (prefixWord ++ tailWord_819705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819705).length < 2 ^ (prefixWord ++ tailWord_819705).sum := by decide
  have hdescent : baseEnd_819705 < baseStart_819705 := by decide
  rcases family_descends (prefixWord ++ tailWord_819705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819715 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_819715 : Nat := 118140960795 + 819715 * 2 ^ 59
def prefixEnd_819715 : Nat := 4983230072969 + 3 ^ 40 * 819715 * 2
def baseEnd_819715 : Nat := 420907794700365594992705

theorem tailTrace_819715 : CollatzResearch.WordTrace tailWord_819715 prefixEnd_819715 420907794700365594992705 := by
  unfold tailWord_819715
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897462225320026021444599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931641483546684014296399 29897462225320026021444599)
  ·
    refine ⟨44846193337980039032166899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29897462225320026021444599 44846193337980039032166899)
    ·
      refine ⟨67269290006970058548250349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44846193337980039032166899 67269290006970058548250349)
      ·
        refine ⟨25225983752613771955593881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67269290006970058548250349 25225983752613771955593881)
        ·
          refine ⟨18919487814460328966695411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25225983752613771955593881 18919487814460328966695411)
          ·
            refine ⟨28379231721690493450043117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18919487814460328966695411 28379231721690493450043117)
            ·
              refine ⟨10642211895633935043766169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28379231721690493450043117 10642211895633935043766169)
              ·
                refine ⟨7981658921725451282824627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642211895633935043766169 7981658921725451282824627)
                ·
                  refine ⟨11972488382588176924236941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981658921725451282824627 11972488382588176924236941)
                  ·
                    refine ⟨4489683143470566346588853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11972488382588176924236941 4489683143470566346588853)
                    ·
                      refine ⟨420907794700365594992705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4489683143470566346588853 420907794700365594992705)
                      ·
                        rfl

theorem cell23_819715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_819715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819715 prefixEnd_819715 := by exact prefixLift 819715
  have htrace : WordTrace (prefixWord ++ tailWord_819715) baseStart_819715 baseEnd_819715 := by
    simpa [prefixWord, tailWord_819715, baseEnd_819715] using wordTrace_append hprefix tailTrace_819715
  have hstable : (prefixWord ++ tailWord_819715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819715).length < 2 ^ (prefixWord ++ tailWord_819715).sum := by decide
  have hdescent : baseEnd_819715 < baseStart_819715 := by decide
  rcases family_descends (prefixWord ++ tailWord_819715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819723 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 2, 1, 3]
def baseStart_819723 : Nat := 118140960795 + 819723 * 2 ^ 59
def prefixEnd_819723 : Nat := 4983230072969 + 3 ^ 40 * 819723 * 2
def baseEnd_819723 : Nat := 420911902545601563692669

theorem tailTrace_819723 : CollatzResearch.WordTrace tailWord_819723 prefixEnd_819723 420911902545601563692669 := by
  unfold tailWord_819723
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897754009291043387735823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931836006194028925157215 29897754009291043387735823)
  ·
    refine ⟨44846631013936565081603735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29897754009291043387735823 44846631013936565081603735)
    ·
      refine ⟨67269946520904847622405603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44846631013936565081603735 67269946520904847622405603)
      ·
        refine ⟨100904919781357271433608405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67269946520904847622405603 100904919781357271433608405)
        ·
          refine ⟨2364959057375561049225197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100904919781357271433608405 2364959057375561049225197)
          ·
            refine ⟨886859646515835393459449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2364959057375561049225197 886859646515835393459449)
            ·
              refine ⟨665144734886876545094587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886859646515835393459449 665144734886876545094587)
              ·
                refine ⟨997717102330314817641881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665144734886876545094587 997717102330314817641881)
                ·
                  refine ⟨748287826747736113231411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 997717102330314817641881 748287826747736113231411)
                  ·
                    refine ⟨1122431740121604169847117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 748287826747736113231411 1122431740121604169847117)
                    ·
                      refine ⟨420911902545601563692669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1122431740121604169847117 420911902545601563692669)
                      ·
                        rfl

theorem cell23_819723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 1, 3].length) (baseStart_819723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819723 prefixEnd_819723 := by exact prefixLift 819723
  have htrace : WordTrace (prefixWord ++ tailWord_819723) baseStart_819723 baseEnd_819723 := by
    simpa [prefixWord, tailWord_819723, baseEnd_819723] using wordTrace_append hprefix tailTrace_819723
  have hstable : (prefixWord ++ tailWord_819723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819723).length < 2 ^ (prefixWord ++ tailWord_819723).sum := by decide
  have hdescent : baseEnd_819723 < baseStart_819723 := by decide
  rcases family_descends (prefixWord ++ tailWord_819723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819729 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_819729 : Nat := 118140960795 + 819729 * 2 ^ 59
def prefixEnd_819729 : Nat := 4983230072969 + 3 ^ 40 * 819729 * 2
def baseEnd_819729 : Nat := 420914983429528540217641

theorem tailTrace_819729 : CollatzResearch.WordTrace tailWord_819729 prefixEnd_819729 420914983429528540217641 := by
  unfold tailWord_819729
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897972847269306412454241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931981898179537608302827 29897972847269306412454241)
  ·
    refine ⟨22423479635451979809340681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29897972847269306412454241 22423479635451979809340681)
    ·
      refine ⟨16817609726588984857005511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22423479635451979809340681 16817609726588984857005511)
      ·
        refine ⟨25226414589883477285508267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16817609726588984857005511 25226414589883477285508267)
        ·
          refine ⟨37839621884825215928262401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25226414589883477285508267 37839621884825215928262401)
          ·
            refine ⟨28379716413618911946196801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37839621884825215928262401 28379716413618911946196801)
            ·
              refine ⟨21284787310214183959647601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28379716413618911946196801 21284787310214183959647601)
              ·
                refine ⟨15963590482660637969735701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21284787310214183959647601 15963590482660637969735701)
                ·
                  refine ⟨748293303874717404831361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15963590482660637969735701 748293303874717404831361)
                  ·
                    refine ⟨561219977906038053623521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748293303874717404831361 561219977906038053623521)
                    ·
                      refine ⟨420914983429528540217641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561219977906038053623521 420914983429528540217641)
                      ·
                        rfl

theorem cell23_819729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_819729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819729 prefixEnd_819729 := by exact prefixLift 819729
  have htrace : WordTrace (prefixWord ++ tailWord_819729) baseStart_819729 baseEnd_819729 := by
    simpa [prefixWord, tailWord_819729, baseEnd_819729] using wordTrace_append hprefix tailTrace_819729
  have hstable : (prefixWord ++ tailWord_819729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819729).length < 2 ^ (prefixWord ++ tailWord_819729).sum := by decide
  have hdescent : baseEnd_819729 < baseStart_819729 := by decide
  rcases family_descends (prefixWord ++ tailWord_819729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819757 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_819757 : Nat := 118140960795 + 819757 * 2 ^ 59
def prefixEnd_819757 : Nat := 4983230072969 + 3 ^ 40 * 819757 * 2
def baseEnd_819757 : Nat := 420929360887854430667513

theorem tailTrace_819757 : CollatzResearch.WordTrace tailWord_819757 prefixEnd_819757 420929360887854430667513 := by
  unfold tailWord_819757
  simp only [CollatzResearch.WordTrace]
  refine ⟨29898994091167867194473525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19932662727445244796315683 29898994091167867194473525)
  ·
    refine ⟨2803030696046987549481893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29898994091167867194473525 2803030696046987549481893)
    ·
      refine ⟨525568255508810165527855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2803030696046987549481893 525568255508810165527855)
      ·
        refine ⟨788352383263215248291783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525568255508810165527855 788352383263215248291783)
        ·
          refine ⟨1182528574894822872437675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788352383263215248291783 1182528574894822872437675)
          ·
            refine ⟨1773792862342234308656513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182528574894822872437675 1773792862342234308656513)
            ·
              refine ⟨1330344646756675731492385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773792862342234308656513 1330344646756675731492385)
              ·
                refine ⟨997758485067506798619289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330344646756675731492385 997758485067506798619289)
                ·
                  refine ⟨748318863800630098964467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 997758485067506798619289 748318863800630098964467)
                  ·
                    refine ⟨1122478295700945148446701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 748318863800630098964467 1122478295700945148446701)
                    ·
                      refine ⟨420929360887854430667513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1122478295700945148446701 420929360887854430667513)
                      ·
                        rfl

theorem cell23_819757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_819757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819757 prefixEnd_819757 := by exact prefixLift 819757
  have htrace : WordTrace (prefixWord ++ tailWord_819757) baseStart_819757 baseEnd_819757 := by
    simpa [prefixWord, tailWord_819757, baseEnd_819757] using wordTrace_append hprefix tailTrace_819757
  have hstable : (prefixWord ++ tailWord_819757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819757).length < 2 ^ (prefixWord ++ tailWord_819757).sum := by decide
  have hdescent : baseEnd_819757 < baseStart_819757 := by decide
  rcases family_descends (prefixWord ++ tailWord_819757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819769 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 5]
def baseStart_819769 : Nat := 118140960795 + 819769 * 2 ^ 59
def prefixEnd_819769 : Nat := 4983230072969 + 3 ^ 40 * 819769 * 2
def baseEnd_819769 : Nat := 46770613628412042635273

theorem tailTrace_819769 : CollatzResearch.WordTrace tailWord_819769 prefixEnd_819769 46770613628412042635273 := by
  unfold tailWord_819769
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899431767124393243910361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19932954511416262162606907 29899431767124393243910361)
  ·
    refine ⟨22424573825343294932932771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29899431767124393243910361 22424573825343294932932771)
    ·
      refine ⟨33636860738014942399399157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22424573825343294932932771 33636860738014942399399157)
      ·
        refine ⟨3153455694188900849943671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33636860738014942399399157 3153455694188900849943671)
        ·
          refine ⟨4730183541283351274915507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153455694188900849943671 4730183541283351274915507)
          ·
            refine ⟨7095275311925026912373261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730183541283351274915507 7095275311925026912373261)
            ·
              refine ⟨2660728241971885092139973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7095275311925026912373261 2660728241971885092139973)
              ·
                refine ⟨498886545369728454776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2660728241971885092139973 498886545369728454776245)
                ·
                  refine ⟨46770613628412042635273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498886545369728454776245 46770613628412042635273)
                  ·
                    rfl

theorem cell23_819769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 5].length) (baseStart_819769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819769 prefixEnd_819769 := by exact prefixLift 819769
  have htrace : WordTrace (prefixWord ++ tailWord_819769) baseStart_819769 baseEnd_819769 := by
    simpa [prefixWord, tailWord_819769, baseEnd_819769] using wordTrace_append hprefix tailTrace_819769
  have hstable : (prefixWord ++ tailWord_819769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819769).length < 2 ^ (prefixWord ++ tailWord_819769).sum := by decide
  have hdescent : baseEnd_819769 < baseStart_819769 := by decide
  rcases family_descends (prefixWord ++ tailWord_819769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819893 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 6]
def baseStart_819893 : Nat := 118140960795 + 819893 * 2 ^ 59
def prefixEnd_819893 : Nat := 4983230072969 + 3 ^ 40 * 819893 * 2
def baseEnd_819893 : Nat := 46777688250762877618543

theorem tailTrace_819893 : CollatzResearch.WordTrace tailWord_819893 prefixEnd_819893 46777688250762877618543 := by
  unfold tailWord_819893
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903954418675162421424333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19935969612450108280949555 29903954418675162421424333)
  ·
    refine ⟨11213982907003185908034125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29903954418675162421424333 11213982907003185908034125)
    ·
      refine ⟨4205243590126194715512797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11213982907003185908034125 4205243590126194715512797)
      ·
        refine ⟨1576966346297323018317299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4205243590126194715512797 1576966346297323018317299)
        ·
          refine ⟨2365449519445984527475949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576966346297323018317299 2365449519445984527475949)
          ·
            refine ⟨887043569792244197803481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2365449519445984527475949 887043569792244197803481)
            ·
              refine ⟨665282677344183148352611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887043569792244197803481 665282677344183148352611)
              ·
                refine ⟨997924016016274722528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665282677344183148352611 997924016016274722528917)
                ·
                  refine ⟨46777688250762877618543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997924016016274722528917 46777688250762877618543)
                  ·
                    rfl

theorem cell23_819893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_819893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819893 prefixEnd_819893 := by exact prefixLift 819893
  have htrace : WordTrace (prefixWord ++ tailWord_819893) baseStart_819893 baseEnd_819893 := by
    simpa [prefixWord, tailWord_819893, baseEnd_819893] using wordTrace_append hprefix tailTrace_819893
  have hstable : (prefixWord ++ tailWord_819893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819893).length < 2 ^ (prefixWord ++ tailWord_819893).sum := by decide
  have hdescent : baseEnd_819893 < baseStart_819893 := by decide
  rcases family_descends (prefixWord ++ tailWord_819893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819937 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_819937 : Nat := 118140960795 + 819937 * 2 ^ 59
def prefixEnd_819937 : Nat := 4983230072969 + 3 ^ 40 * 819937 * 2
def baseEnd_819937 : Nat := 421021787405663726416685

theorem tailTrace_819937 : CollatzResearch.WordTrace tailWord_819937 prefixEnd_819937 421021787405663726416685 := by
  unfold tailWord_819937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29905559230515757936026065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19937039487010505290684043 29905559230515757936026065)
  ·
    refine ⟨22429169422886818452019549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29905559230515757936026065 22429169422886818452019549)
    ·
      refine ⟨8410938533582556919507331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22429169422886818452019549 8410938533582556919507331)
      ·
        refine ⟨12616407800373835379260997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410938533582556919507331 12616407800373835379260997)
        ·
          refine ⟨2365576462570094133611437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12616407800373835379260997 2365576462570094133611437)
          ·
            refine ⟨887091173463785300104289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2365576462570094133611437 887091173463785300104289)
            ·
              refine ⟨665318380097838975078217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887091173463785300104289 665318380097838975078217)
              ·
                refine ⟨498988785073379231308663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665318380097838975078217 498988785073379231308663)
                ·
                  refine ⟨748483177610068846962995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498988785073379231308663 748483177610068846962995)
                  ·
                    refine ⟨1122724766415103270444493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 748483177610068846962995 1122724766415103270444493)
                    ·
                      refine ⟨421021787405663726416685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1122724766415103270444493 421021787405663726416685)
                      ·
                        rfl

theorem cell23_819937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_819937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819937 prefixEnd_819937 := by exact prefixLift 819937
  have htrace : WordTrace (prefixWord ++ tailWord_819937) baseStart_819937 baseEnd_819937 := by
    simpa [prefixWord, tailWord_819937, baseEnd_819937] using wordTrace_append hprefix tailTrace_819937
  have hstable : (prefixWord ++ tailWord_819937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819937).length < 2 ^ (prefixWord ++ tailWord_819937).sum := by decide
  have hdescent : baseEnd_819937 < baseStart_819937 := by decide
  rcases family_descends (prefixWord ++ tailWord_819937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819976 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_819976 : Nat := 118140960795 + 819976 * 2 ^ 59
def prefixEnd_819976 : Nat := 4983230072969 + 3 ^ 40 * 819976 * 2
def baseEnd_819976 : Nat := 421041813151189073829005

theorem tailTrace_819976 : CollatzResearch.WordTrace tailWord_819976 prefixEnd_819976 421041813151189073829005 := by
  unfold tailWord_819976
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953490838687233798347891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19937987784916311731130521 14953490838687233798347891)
  ·
    refine ⟨22430236258030850697521837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14953490838687233798347891 22430236258030850697521837)
    ·
      refine ⟨8411338596761569011570689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22430236258030850697521837 8411338596761569011570689)
      ·
        refine ⟨6308503947571176758678017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8411338596761569011570689 6308503947571176758678017)
        ·
          refine ⟨4731377960678382569008513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308503947571176758678017 4731377960678382569008513)
          ·
            refine ⟨3548533470508786926756385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731377960678382569008513 3548533470508786926756385)
            ·
              refine ⟨2661400102881590195067289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548533470508786926756385 2661400102881590195067289)
              ·
                refine ⟨1996050077161192646300467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661400102881590195067289 1996050077161192646300467)
                ·
                  refine ⟨2994075115741788969450701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996050077161192646300467 2994075115741788969450701)
                  ·
                    refine ⟨1122778168403170863544013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994075115741788969450701 1122778168403170863544013)
                    ·
                      refine ⟨421041813151189073829005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1122778168403170863544013 421041813151189073829005)
                      ·
                        rfl

theorem cell23_819976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_819976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_819976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_819976 prefixEnd_819976 := by exact prefixLift 819976
  have htrace : WordTrace (prefixWord ++ tailWord_819976) baseStart_819976 baseEnd_819976 := by
    simpa [prefixWord, tailWord_819976, baseEnd_819976] using wordTrace_append hprefix tailTrace_819976
  have hstable : (prefixWord ++ tailWord_819976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819976).length < 2 ^ (prefixWord ++ tailWord_819976).sum := by decide
  have hdescent : baseEnd_819976 < baseStart_819976 := by decide
  rcases family_descends (prefixWord ++ tailWord_819976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820050 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_820050 : Nat := 118140960795 + 820050 * 2 ^ 59
def prefixEnd_820050 : Nat := 4983230072969 + 3 ^ 40 * 820050 * 2
def baseEnd_820050 : Nat := 421079810719621784303665

theorem tailTrace_820050 : CollatzResearch.WordTrace tailWord_820050 prefixEnd_820050 421079810719621784303665 := by
  unfold tailWord_820050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477420169776594558722401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19939787119404252156593069 7477420169776594558722401)
  ·
    refine ⟨5608065127332445919041801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7477420169776594558722401 5608065127332445919041801)
    ·
      refine ⟨4206048845499334439281351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5608065127332445919041801 4206048845499334439281351)
      ·
        refine ⟨6309073268249001658922027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206048845499334439281351 6309073268249001658922027)
        ·
          refine ⟨9463609902373502488383041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309073268249001658922027 9463609902373502488383041)
          ·
            refine ⟨7097707426780126866287281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9463609902373502488383041 7097707426780126866287281)
            ·
              refine ⟨5323280570085095149715461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097707426780126866287281 5323280570085095149715461)
              ·
                refine ⟨998115106890955340571649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5323280570085095149715461 998115106890955340571649)
                ·
                  refine ⟨748586330168216505428737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998115106890955340571649 748586330168216505428737)
                  ·
                    refine ⟨561439747626162379071553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748586330168216505428737 561439747626162379071553)
                    ·
                      refine ⟨421079810719621784303665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561439747626162379071553 421079810719621784303665)
                      ·
                        rfl

theorem cell23_820050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_820050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820050 prefixEnd_820050 := by exact prefixLift 820050
  have htrace : WordTrace (prefixWord ++ tailWord_820050) baseStart_820050 baseEnd_820050 := by
    simpa [prefixWord, tailWord_820050, baseEnd_820050] using wordTrace_append hprefix tailTrace_820050
  have hstable : (prefixWord ++ tailWord_820050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820050).length < 2 ^ (prefixWord ++ tailWord_820050).sum := by decide
  have hdescent : baseEnd_820050 < baseStart_820050 := by decide
  rcases family_descends (prefixWord ++ tailWord_820050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820056 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 5]
def baseStart_820056 : Nat := 118140960795 + 820056 * 2 ^ 59
def prefixEnd_820056 : Nat := 4983230072969 + 3 ^ 40 * 820056 * 2
def baseEnd_820056 : Nat := 46786987955949862314293

theorem tailTrace_820056 : CollatzResearch.WordTrace tailWord_820056 prefixEnd_820056 46786987955949862314293 := by
  unfold tailWord_820056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954949758542320629804011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19939933011389760839738681 14954949758542320629804011)
  ·
    refine ⟨22432424637813480944706017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14954949758542320629804011 22432424637813480944706017)
    ·
      refine ⟨16824318478360110708529513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22432424637813480944706017 16824318478360110708529513)
      ·
        refine ⟨12618238858770083031397135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16824318478360110708529513 12618238858770083031397135)
        ·
          refine ⟨18927358288155124547095703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12618238858770083031397135 18927358288155124547095703)
          ·
            refine ⟨28391037432232686820643555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18927358288155124547095703 28391037432232686820643555)
            ·
              refine ⟨42586556148349030230965333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28391037432232686820643555 42586556148349030230965333)
              ·
                refine ⟨499061204863465198019125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42586556148349030230965333 499061204863465198019125)
                ·
                  refine ⟨46786987955949862314293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499061204863465198019125 46786987955949862314293)
                  ·
                    rfl

theorem cell23_820056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 5].length) (baseStart_820056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820056 prefixEnd_820056 := by exact prefixLift 820056
  have htrace : WordTrace (prefixWord ++ tailWord_820056) baseStart_820056 baseEnd_820056 := by
    simpa [prefixWord, tailWord_820056, baseEnd_820056] using wordTrace_append hprefix tailTrace_820056
  have hstable : (prefixWord ++ tailWord_820056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820056).length < 2 ^ (prefixWord ++ tailWord_820056).sum := by decide
  have hdescent : baseEnd_820056 < baseStart_820056 := by decide
  rcases family_descends (prefixWord ++ tailWord_820056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820067 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 2, 2, 2]
def baseStart_820067 : Nat := 118140960795 + 820067 * 2 ^ 59
def prefixEnd_820067 : Nat := 4983230072969 + 3 ^ 40 * 820067 * 2
def baseEnd_820067 : Nat := 421088539890748217791087

theorem tailTrace_820067 : CollatzResearch.WordTrace tailWord_820067 prefixEnd_820067 421088539890748217791087 := by
  unfold tailWord_820067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910300720044790138258455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19940200480029860092172303 29910300720044790138258455)
  ·
    refine ⟨44865451080067185207387683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29910300720044790138258455 44865451080067185207387683)
    ·
      refine ⟨67298176620100777811081525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44865451080067185207387683 67298176620100777811081525)
      ·
        refine ⟨6309204058134447919788893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67298176620100777811081525 6309204058134447919788893)
        ·
          refine ⟨2365951521800417969920835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309204058134447919788893 2365951521800417969920835)
          ·
            refine ⟨3548927282700626954881253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365951521800417969920835 3548927282700626954881253)
            ·
              refine ⟨665423865506367554040235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3548927282700626954881253 665423865506367554040235)
              ·
                refine ⟨998135798259551331060353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665423865506367554040235 998135798259551331060353)
                ·
                  refine ⟨748601848694663498295265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998135798259551331060353 748601848694663498295265)
                  ·
                    refine ⟨561451386520997623721449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748601848694663498295265 561451386520997623721449)
                    ·
                      refine ⟨421088539890748217791087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561451386520997623721449 421088539890748217791087)
                      ·
                        rfl

theorem cell23_820067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_820067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820067 prefixEnd_820067 := by exact prefixLift 820067
  have htrace : WordTrace (prefixWord ++ tailWord_820067) baseStart_820067 baseEnd_820067 := by
    simpa [prefixWord, tailWord_820067, baseEnd_820067] using wordTrace_append hprefix tailTrace_820067
  have hstable : (prefixWord ++ tailWord_820067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820067).length < 2 ^ (prefixWord ++ tailWord_820067).sum := by decide
  have hdescent : baseEnd_820067 < baseStart_820067 := by decide
  rcases family_descends (prefixWord ++ tailWord_820067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820069 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_820069 : Nat := 118140960795 + 820069 * 2 ^ 59
def prefixEnd_820069 : Nat := 4983230072969 + 3 ^ 40 * 820069 * 2
def baseEnd_820069 : Nat := 140363188950685736655359

theorem tailTrace_820069 : CollatzResearch.WordTrace tailWord_820069 prefixEnd_820069 140363188950685736655359 := by
  unfold tailWord_820069
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910373666037544479831261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19940249110691696319887507 29910373666037544479831261)
  ·
    refine ⟨11216390124764079179936723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29910373666037544479831261 11216390124764079179936723)
    ·
      refine ⟨16824585187146118769905085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216390124764079179936723 16824585187146118769905085)
      ·
        refine ⟨6309219445179794538714407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16824585187146118769905085 6309219445179794538714407)
        ·
          refine ⟨9463829167769691808071611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309219445179794538714407 9463829167769691808071611)
          ·
            refine ⟨14195743751654537712107417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463829167769691808071611 14195743751654537712107417)
            ·
              refine ⟨10646807813740903284080563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195743751654537712107417 10646807813740903284080563)
              ·
                refine ⟨15970211720611354926120845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646807813740903284080563 15970211720611354926120845)
                ·
                  refine ⟨5988829395229258097295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15970211720611354926120845 5988829395229258097295317)
                  ·
                    refine ⟨140363188950685736655359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5988829395229258097295317 140363188950685736655359)
                    ·
                      rfl

theorem cell23_820069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_820069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820069 prefixEnd_820069 := by exact prefixLift 820069
  have htrace : WordTrace (prefixWord ++ tailWord_820069) baseStart_820069 baseEnd_820069 := by
    simpa [prefixWord, tailWord_820069, baseEnd_820069] using wordTrace_append hprefix tailTrace_820069
  have hstable : (prefixWord ++ tailWord_820069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820069).length < 2 ^ (prefixWord ++ tailWord_820069).sum := by decide
  have hdescent : baseEnd_820069 < baseStart_820069 := by decide
  rcases family_descends (prefixWord ++ tailWord_820069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820180 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 6]
def baseStart_820180 : Nat := 118140960795 + 820180 * 2 ^ 59
def prefixEnd_820180 : Nat := 4983230072969 + 3 ^ 40 * 820180 * 2
def baseEnd_820180 : Nat := 46794062578300697297563

theorem tailTrace_820180 : CollatzResearch.WordTrace tailWord_820180 prefixEnd_820180 46794062578300697297563 := by
  unfold tailWord_820180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957211084317705218560997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19942948112423606958081329 14957211084317705218560997)
  ·
    refine ⟨2804477078309569728480187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14957211084317705218560997 2804477078309569728480187)
    ·
      refine ⟨4206715617464354592720281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804477078309569728480187 4206715617464354592720281)
      ·
        refine ⟨3155036713098265944540211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4206715617464354592720281 3155036713098265944540211)
        ·
          refine ⟨4732555069647398916810317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155036713098265944540211 4732555069647398916810317)
          ·
            refine ⟨1774708151117774593803869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4732555069647398916810317 1774708151117774593803869)
            ·
              refine ⟨665515556669165472676451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1774708151117774593803869 665515556669165472676451)
              ·
                refine ⟨998273335003748209014677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665515556669165472676451 998273335003748209014677)
                ·
                  refine ⟨46794062578300697297563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 998273335003748209014677 46794062578300697297563)
                  ·
                    rfl

theorem cell23_820180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_820180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820180 prefixEnd_820180 := by exact prefixLift 820180
  have htrace : WordTrace (prefixWord ++ tailWord_820180) baseStart_820180 baseEnd_820180 := by
    simpa [prefixWord, tailWord_820180, baseEnd_820180] using wordTrace_append hprefix tailTrace_820180
  have hstable : (prefixWord ++ tailWord_820180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820180).length < 2 ^ (prefixWord ++ tailWord_820180).sum := by decide
  have hdescent : baseEnd_820180 < baseStart_820180 := by decide
  rcases family_descends (prefixWord ++ tailWord_820180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820183 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_820183 : Nat := 118140960795 + 820183 * 2 ^ 59
def prefixEnd_820183 : Nat := 4983230072969 + 3 ^ 40 * 820183 * 2
def baseEnd_820183 : Nat := 421148103646669763940553

theorem tailTrace_820183 : CollatzResearch.WordTrace tailWord_820183 prefixEnd_820183 421148103646669763940553 := by
  unfold tailWord_820183
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914531587624541949481203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19943021058416361299654135 29914531587624541949481203)
  ·
    refine ⟨44871797381436812924221805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29914531587624541949481203 44871797381436812924221805)
    ·
      refine ⟨16826924018038804846583177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44871797381436812924221805 16826924018038804846583177)
      ·
        refine ⟨12620193013529103634937383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16826924018038804846583177 12620193013529103634937383)
        ·
          refine ⟨18930289520293655452406075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12620193013529103634937383 18930289520293655452406075)
          ·
            refine ⟨28395434280440483178609113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18930289520293655452406075 28395434280440483178609113)
            ·
              refine ⟨21296575710330362383956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28395434280440483178609113 21296575710330362383956835)
              ·
                refine ⟨31944863565495543575935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21296575710330362383956835 31944863565495543575935253)
                ·
                  refine ⟨1497415479632603605121965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31944863565495543575935253 1497415479632603605121965)
                  ·
                    refine ⟨561530804862226351920737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497415479632603605121965 561530804862226351920737)
                    ·
                      refine ⟨421148103646669763940553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561530804862226351920737 421148103646669763940553)
                      ·
                        rfl

theorem cell23_820183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_820183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820183 prefixEnd_820183 := by exact prefixLift 820183
  have htrace : WordTrace (prefixWord ++ tailWord_820183) baseStart_820183 baseEnd_820183 := by
    simpa [prefixWord, tailWord_820183, baseEnd_820183] using wordTrace_append hprefix tailTrace_820183
  have hstable : (prefixWord ++ tailWord_820183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820183).length < 2 ^ (prefixWord ++ tailWord_820183).sum := by decide
  have hdescent : baseEnd_820183 < baseStart_820183 := by decide
  rcases family_descends (prefixWord ++ tailWord_820183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820207 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 1, 1, 3]
def baseStart_820207 : Nat := 118140960795 + 820207 * 2 ^ 59
def prefixEnd_820207 : Nat := 4983230072969 + 3 ^ 40 * 820207 * 2
def baseEnd_820207 : Nat := 421160427182377670040443

theorem tailTrace_820207 : CollatzResearch.WordTrace tailWord_820207 prefixEnd_820207 421160427182377670040443 := by
  unfold tailWord_820207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29915406939537594048354875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19943604626358396032236583 29915406939537594048354875)
  ·
    refine ⟨44873110409306391072532313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29915406939537594048354875 44873110409306391072532313)
    ·
      refine ⟨33654832806979793304399235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44873110409306391072532313 33654832806979793304399235)
      ·
        refine ⟨50482249210469689956598853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33654832806979793304399235 50482249210469689956598853)
        ·
          refine ⟨9465421726963066866862285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50482249210469689956598853 9465421726963066866862285)
          ·
            refine ⟨3549533147611150075073357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9465421726963066866862285 3549533147611150075073357)
            ·
              refine ⟨1331074930354181278152509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3549533147611150075073357 1331074930354181278152509)
              ·
                refine ⟨499153098882817979307191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1331074930354181278152509 499153098882817979307191)
                ·
                  refine ⟨748729648324226968960787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499153098882817979307191 748729648324226968960787)
                  ·
                    refine ⟨1123094472486340453441181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 748729648324226968960787 1123094472486340453441181)
                    ·
                      refine ⟨421160427182377670040443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1123094472486340453441181 421160427182377670040443)
                      ·
                        rfl

theorem cell23_820207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 1, 3].length) (baseStart_820207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820207 prefixEnd_820207 := by exact prefixLift 820207
  have htrace : WordTrace (prefixWord ++ tailWord_820207) baseStart_820207 baseEnd_820207 := by
    simpa [prefixWord, tailWord_820207, baseEnd_820207] using wordTrace_append hprefix tailTrace_820207
  have hstable : (prefixWord ++ tailWord_820207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820207).length < 2 ^ (prefixWord ++ tailWord_820207).sum := by decide
  have hdescent : baseEnd_820207 < baseStart_820207 := by decide
  rcases family_descends (prefixWord ++ tailWord_820207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820236 : List Nat := [2, 2, 1, 2, 3, 2, 1, 10]
def baseStart_820236 : Nat := 118140960795 + 820236 * 2 ^ 59
def prefixEnd_820236 : Nat := 4983230072969 + 3 ^ 40 * 820236 * 2
def baseEnd_820236 : Nat := 15599085856346594688067

theorem tailTrace_820236 : CollatzResearch.WordTrace tailWord_820236 prefixEnd_820236 15599085856346594688067 := by
  unfold tailWord_820236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958232328216266000580281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19944309770955021334107041 14958232328216266000580281)
  ·
    refine ⟨11218674246162199500435211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14958232328216266000580281 11218674246162199500435211)
    ·
      refine ⟨16828011369243299250652817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11218674246162199500435211 16828011369243299250652817)
      ·
        refine ⟨12621008526932474437989613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16828011369243299250652817 12621008526932474437989613)
        ·
          refine ⟨4732878197599677914246105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12621008526932474437989613 4732878197599677914246105)
          ·
            refine ⟨3549658648199758435684579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4732878197599677914246105 3549658648199758435684579)
            ·
              refine ⟨5324487972299637653526869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549658648199758435684579 5324487972299637653526869)
              ·
                refine ⟨15599085856346594688067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5324487972299637653526869 15599085856346594688067)
                ·
                  rfl

theorem cell23_820236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 10].length) (baseStart_820236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820236 prefixEnd_820236 := by exact prefixLift 820236
  have htrace : WordTrace (prefixWord ++ tailWord_820236) baseStart_820236 baseEnd_820236 := by
    simpa [prefixWord, tailWord_820236, baseEnd_820236] using wordTrace_append hprefix tailTrace_820236
  have hstable : (prefixWord ++ tailWord_820236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820236).length < 2 ^ (prefixWord ++ tailWord_820236).sum := by decide
  have hdescent : baseEnd_820236 < baseStart_820236 := by decide
  rcases family_descends (prefixWord ++ tailWord_820236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820247 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_820247 : Nat := 118140960795 + 820247 * 2 ^ 59
def prefixEnd_820247 : Nat := 4983230072969 + 3 ^ 40 * 820247 * 2
def baseEnd_820247 : Nat := 421180966408557513540259

theorem tailTrace_820247 : CollatzResearch.WordTrace tailWord_820247 prefixEnd_820247 421180966408557513540259 := by
  unfold tailWord_820247
  simp only [CollatzResearch.WordTrace]
  refine ⟨29916865859392680879810995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19944577239595120586540663 29916865859392680879810995)
  ·
    refine ⟨44875298789089021319716493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29916865859392680879810995 44875298789089021319716493)
    ·
      refine ⟨16828237045908382994893685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44875298789089021319716493 16828237045908382994893685)
      ·
        refine ⟨1577647223053910905771283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16828237045908382994893685 1577647223053910905771283)
        ·
          refine ⟨2366470834580866358656925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577647223053910905771283 2366470834580866358656925)
          ·
            refine ⟨887426562967824884496347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2366470834580866358656925 887426562967824884496347)
            ·
              refine ⟨1331139844451737326744521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887426562967824884496347 1331139844451737326744521)
              ·
                refine ⟨998354883338802995058391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331139844451737326744521 998354883338802995058391)
                ·
                  refine ⟨1497532325008204492587587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998354883338802995058391 1497532325008204492587587)
                  ·
                    refine ⟨2246298487512306738881381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1497532325008204492587587 2246298487512306738881381)
                    ·
                      refine ⟨421180966408557513540259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2246298487512306738881381 421180966408557513540259)
                      ·
                        rfl

theorem cell23_820247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_820247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820247 prefixEnd_820247 := by exact prefixLift 820247
  have htrace : WordTrace (prefixWord ++ tailWord_820247) baseStart_820247 baseEnd_820247 := by
    simpa [prefixWord, tailWord_820247, baseEnd_820247] using wordTrace_append hprefix tailTrace_820247
  have hstable : (prefixWord ++ tailWord_820247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820247).length < 2 ^ (prefixWord ++ tailWord_820247).sum := by decide
  have hdescent : baseEnd_820247 < baseStart_820247 := by decide
  rcases family_descends (prefixWord ++ tailWord_820247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820260 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_820260 : Nat := 118140960795 + 820260 * 2 ^ 59
def prefixEnd_820260 : Nat := 4983230072969 + 3 ^ 40 * 820260 * 2
def baseEnd_820260 : Nat := 421187641657065962677699

theorem tailTrace_820260 : CollatzResearch.WordTrace tailWord_820260 prefixEnd_820260 421187641657065962677699 := by
  unfold tailWord_820260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958670004172792050017117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19944893338897056066689489 14958670004172792050017117)
  ·
    refine ⟨5609501251564797018756419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14958670004172792050017117 5609501251564797018756419)
    ·
      refine ⟨8414251877347195528134629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5609501251564797018756419 8414251877347195528134629)
      ·
        refine ⟨1577672227002599161525243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8414251877347195528134629 1577672227002599161525243)
        ·
          refine ⟨2366508340503898742287865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577672227002599161525243 2366508340503898742287865)
          ·
            refine ⟨1774881255377924056715899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366508340503898742287865 1774881255377924056715899)
            ·
              refine ⟨2662321883066886085073849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774881255377924056715899 2662321883066886085073849)
              ·
                refine ⟨1996741412300164563805387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662321883066886085073849 1996741412300164563805387)
                ·
                  refine ⟨2995112118450246845708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996741412300164563805387 2995112118450246845708081)
                  ·
                    refine ⟨2246334088837685134281061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995112118450246845708081 2246334088837685134281061)
                    ·
                      refine ⟨421187641657065962677699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2246334088837685134281061 421187641657065962677699)
                      ·
                        rfl

theorem cell23_820260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_820260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820260 prefixEnd_820260 := by exact prefixLift 820260
  have htrace : WordTrace (prefixWord ++ tailWord_820260) baseStart_820260 baseEnd_820260 := by
    simpa [prefixWord, tailWord_820260, baseEnd_820260] using wordTrace_append hprefix tailTrace_820260
  have hstable : (prefixWord ++ tailWord_820260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820260).length < 2 ^ (prefixWord ++ tailWord_820260).sum := by decide
  have hdescent : baseEnd_820260 < baseStart_820260 := by decide
  rcases family_descends (prefixWord ++ tailWord_820260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820281 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 1, 2, 2]
def baseStart_820281 : Nat := 118140960795 + 820281 * 2 ^ 59
def prefixEnd_820281 : Nat := 4983230072969 + 3 ^ 40 * 820281 * 2
def baseEnd_820281 : Nat := 421198424750810380515103

theorem tailTrace_820281 : CollatzResearch.WordTrace tailWord_820281 prefixEnd_820281 421198424750810380515103 := by
  unfold tailWord_820281
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918105941269504686548697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19945403960846336457699131 29918105941269504686548697)
  ·
    refine ⟨22438579455952128514911523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29918105941269504686548697 22438579455952128514911523)
    ·
      refine ⟨33657869183928192772367285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22438579455952128514911523 33657869183928192772367285)
      ·
        refine ⟨3155425235993268072409433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33657869183928192772367285 3155425235993268072409433)
        ·
          refine ⟨2366568926994951054307075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3155425235993268072409433 2366568926994951054307075)
          ·
            refine ⟨3549853390492426581460613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366568926994951054307075 3549853390492426581460613)
            ·
              refine ⟨665597510717329984023865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3549853390492426581460613 665597510717329984023865)
              ·
                refine ⟨499198133037997488017899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665597510717329984023865 499198133037997488017899)
                ·
                  refine ⟨748797199556996232026849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499198133037997488017899 748797199556996232026849)
                  ·
                    refine ⟨561597899667747174020137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748797199556996232026849 561597899667747174020137)
                    ·
                      refine ⟨421198424750810380515103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561597899667747174020137 421198424750810380515103)
                      ·
                        rfl

theorem cell23_820281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_820281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820281 prefixEnd_820281 := by exact prefixLift 820281
  have htrace : WordTrace (prefixWord ++ tailWord_820281) baseStart_820281 baseEnd_820281 := by
    simpa [prefixWord, tailWord_820281, baseEnd_820281] using wordTrace_append hprefix tailTrace_820281
  have hstable : (prefixWord ++ tailWord_820281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820281).length < 2 ^ (prefixWord ++ tailWord_820281).sum := by decide
  have hdescent : baseEnd_820281 < baseStart_820281 := by decide
  rcases family_descends (prefixWord ++ tailWord_820281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820318 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_820318 : Nat := 118140960795 + 820318 * 2 ^ 59
def prefixEnd_820318 : Nat := 4983230072969 + 3 ^ 40 * 820318 * 2
def baseEnd_820318 : Nat := 421217423535026735752433

theorem tailTrace_820318 : CollatzResearch.WordTrace tailWord_820318 prefixEnd_820318 421217423535026735752433 := by
  unfold tailWord_820318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739931930266932500705701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19946303628090306670430405 3739931930266932500705701)
  ·
    refine ⟨701237236925049843882319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3739931930266932500705701 701237236925049843882319)
    ·
      refine ⟨1051855855387574765823479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701237236925049843882319 1051855855387574765823479)
      ·
        refine ⟨1577783783081362148735219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051855855387574765823479 1577783783081362148735219)
        ·
          refine ⟨2366675674622043223102829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577783783081362148735219 2366675674622043223102829)
          ·
            refine ⟨887503377983266208663561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2366675674622043223102829 887503377983266208663561)
            ·
              refine ⟨665627533487449656497671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887503377983266208663561 665627533487449656497671)
              ·
                refine ⟨998441300231174484746507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665627533487449656497671 998441300231174484746507)
                ·
                  refine ⟨1497661950346761727119761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998441300231174484746507 1497661950346761727119761)
                  ·
                    refine ⟨1123246462760071295339821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497661950346761727119761 1123246462760071295339821)
                    ·
                      refine ⟨421217423535026735752433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1123246462760071295339821 421217423535026735752433)
                      ·
                        rfl

theorem cell23_820318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_820318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820318 prefixEnd_820318 := by exact prefixLift 820318
  have htrace : WordTrace (prefixWord ++ tailWord_820318) baseStart_820318 baseEnd_820318 := by
    simpa [prefixWord, tailWord_820318, baseEnd_820318] using wordTrace_append hprefix tailTrace_820318
  have hstable : (prefixWord ++ tailWord_820318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820318).length < 2 ^ (prefixWord ++ tailWord_820318).sum := by decide
  have hdescent : baseEnd_820318 < baseStart_820318 := by decide
  rcases family_descends (prefixWord ++ tailWord_820318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820320 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2]
def baseStart_820320 : Nat := 118140960795 + 820320 * 2 ^ 59
def prefixEnd_820320 : Nat := 4983230072969 + 3 ^ 40 * 820320 * 2
def baseEnd_820320 : Nat := 421218450496335727927423

theorem tailTrace_820320 : CollatzResearch.WordTrace tailWord_820320 prefixEnd_820320 421218450496335727927423 := by
  unfold tailWord_820320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959764194064107173609207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19946352258752142898145609 14959764194064107173609207)
  ·
    refine ⟨22439646291096160760413811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14959764194064107173609207 22439646291096160760413811)
    ·
      refine ⟨33659469436644241140620717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22439646291096160760413811 33659469436644241140620717)
      ·
        refine ⟨12622301038741590427732769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33659469436644241140620717 12622301038741590427732769)
        ·
          refine ⟨9466725779056192820799577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12622301038741590427732769 9466725779056192820799577)
          ·
            refine ⟨7100044334292144615599683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9466725779056192820799577 7100044334292144615599683)
            ·
              refine ⟨10650066501438216923399525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100044334292144615599683 10650066501438216923399525)
              ·
                refine ⟨1996887469019665673137411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10650066501438216923399525 1996887469019665673137411)
                ·
                  refine ⟨2995331203529498509706117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996887469019665673137411 2995331203529498509706117)
                  ·
                    refine ⟨561624600661780970569897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995331203529498509706117 561624600661780970569897)
                    ·
                      refine ⟨421218450496335727927423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561624600661780970569897 421218450496335727927423)
                      ·
                        rfl

theorem cell23_820320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_820320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820320 prefixEnd_820320 := by exact prefixLift 820320
  have htrace : WordTrace (prefixWord ++ tailWord_820320) baseStart_820320 baseEnd_820320 := by
    simpa [prefixWord, tailWord_820320, baseEnd_820320] using wordTrace_append hprefix tailTrace_820320
  have hstable : (prefixWord ++ tailWord_820320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820320).length < 2 ^ (prefixWord ++ tailWord_820320).sum := by decide
  have hdescent : baseEnd_820320 < baseStart_820320 := by decide
  rcases family_descends (prefixWord ++ tailWord_820320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820337 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_820337 : Nat := 118140960795 + 820337 * 2 ^ 59
def prefixEnd_820337 : Nat := 4983230072969 + 3 ^ 40 * 820337 * 2
def baseEnd_820337 : Nat := 421227179667462161414845

theorem tailTrace_820337 : CollatzResearch.WordTrace tailWord_820337 prefixEnd_820337 421227179667462161414845 := by
  unfold tailWord_820337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29920148429066626250587265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19946765619377750833724843 29920148429066626250587265)
  ·
    refine ⟨22440111321799969687940449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29920148429066626250587265 22440111321799969687940449)
    ·
      refine ⟨16830083491349977265955337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22440111321799969687940449 16830083491349977265955337)
      ·
        refine ⟨12622562618512482949466503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16830083491349977265955337 12622562618512482949466503)
        ·
          refine ⟨18933843927768724424199755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622562618512482949466503 18933843927768724424199755)
          ·
            refine ⟨28400765891653086636299633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18933843927768724424199755 28400765891653086636299633)
            ·
              refine ⟨21300574418739814977224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28400765891653086636299633 21300574418739814977224725)
              ·
                refine ⟨998464425878428827057409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21300574418739814977224725 998464425878428827057409)
                ·
                  refine ⟨748848319408821620293057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998464425878428827057409 748848319408821620293057)
                  ·
                    refine ⟨561636239556616215219793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748848319408821620293057 561636239556616215219793)
                    ·
                      refine ⟨421227179667462161414845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561636239556616215219793 421227179667462161414845)
                      ·
                        rfl

theorem cell23_820337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_820337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820337 prefixEnd_820337 := by exact prefixLift 820337
  have htrace : WordTrace (prefixWord ++ tailWord_820337) baseStart_820337 baseEnd_820337 := by
    simpa [prefixWord, tailWord_820337, baseEnd_820337] using wordTrace_append hprefix tailTrace_820337
  have hstable : (prefixWord ++ tailWord_820337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820337).length < 2 ^ (prefixWord ++ tailWord_820337).sum := by decide
  have hdescent : baseEnd_820337 < baseStart_820337 := by decide
  rcases family_descends (prefixWord ++ tailWord_820337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820343 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 7]
def baseStart_820343 : Nat := 118140960795 + 820343 * 2 ^ 59
def prefixEnd_820343 : Nat := 4983230072969 + 3 ^ 40 * 820343 * 2
def baseEnd_820343 : Nat := 46803362283487681993313

theorem tailTrace_820343 : CollatzResearch.WordTrace tailWord_820343 prefixEnd_820343 46803362283487681993313 := by
  unfold tailWord_820343
  simp only [CollatzResearch.WordTrace]
  refine ⟨29920367267044889275305683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19946911511363259516870455 29920367267044889275305683)
  ·
    refine ⟨44880550900567333912958525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29920367267044889275305683 44880550900567333912958525)
    ·
      refine ⟨16830206587712750217359447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44880550900567333912958525 16830206587712750217359447)
      ·
        refine ⟨25245309881569125326039171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16830206587712750217359447 25245309881569125326039171)
        ·
          refine ⟨37867964822353687989058757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25245309881569125326039171 37867964822353687989058757)
          ·
            refine ⟨7100243404191316497948517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37867964822353687989058757 7100243404191316497948517)
            ·
              refine ⟨1331295638285871843365347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7100243404191316497948517 1331295638285871843365347)
              ·
                refine ⟨1996943457428807765048021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331295638285871843365347 1996943457428807765048021)
                ·
                  refine ⟨46803362283487681993313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1996943457428807765048021 46803362283487681993313)
                  ·
                    rfl

theorem cell23_820343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 7].length) (baseStart_820343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820343 prefixEnd_820343 := by exact prefixLift 820343
  have htrace : WordTrace (prefixWord ++ tailWord_820343) baseStart_820343 baseEnd_820343 := by
    simpa [prefixWord, tailWord_820343, baseEnd_820343] using wordTrace_append hprefix tailTrace_820343
  have hstable : (prefixWord ++ tailWord_820343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820343).length < 2 ^ (prefixWord ++ tailWord_820343).sum := by decide
  have hdescent : baseEnd_820343 < baseStart_820343 := by decide
  rcases family_descends (prefixWord ++ tailWord_820343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820410 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_820410 : Nat := 118140960795 + 820410 * 2 ^ 59
def prefixEnd_820410 : Nat := 4983230072969 + 3 ^ 40 * 820410 * 2
def baseEnd_820410 : Nat := 421264663755240375802009

theorem tailTrace_820410 : CollatzResearch.WordTrace tailWord_820410 prefixEnd_820410 421264663755240375802009 := by
  unfold tailWord_820410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480702739450539929498671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19948540638534773145329789 7480702739450539929498671)
  ·
    refine ⟨11221054109175809894248007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480702739450539929498671 11221054109175809894248007)
    ·
      refine ⟨16831581163763714841372011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221054109175809894248007 16831581163763714841372011)
      ·
        refine ⟨25247371745645572262058017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831581163763714841372011 25247371745645572262058017)
        ·
          refine ⟨18935528809234179196543513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25247371745645572262058017 18935528809234179196543513)
          ·
            refine ⟨14201646606925634397407635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935528809234179196543513 14201646606925634397407635)
            ·
              refine ⟨21302469910388451596111453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14201646606925634397407635 21302469910388451596111453)
              ·
                refine ⟨7988426216395669348541795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21302469910388451596111453 7988426216395669348541795)
                ·
                  refine ⟨11982639324593504022812693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988426216395669348541795 11982639324593504022812693)
                  ·
                    refine ⟨561686218340320501069345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11982639324593504022812693 561686218340320501069345)
                    ·
                      refine ⟨421264663755240375802009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561686218340320501069345 421264663755240375802009)
                      ·
                        rfl

theorem cell23_820410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_820410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820410 prefixEnd_820410 := by exact prefixLift 820410
  have htrace : WordTrace (prefixWord ++ tailWord_820410) baseStart_820410 baseEnd_820410 := by
    simpa [prefixWord, tailWord_820410, baseEnd_820410] using wordTrace_append hprefix tailTrace_820410
  have hstable : (prefixWord ++ tailWord_820410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820410).length < 2 ^ (prefixWord ++ tailWord_820410).sum := by decide
  have hdescent : baseEnd_820410 < baseStart_820410 := by decide
  rcases family_descends (prefixWord ++ tailWord_820410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820423 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_820423 : Nat := 118140960795 + 820423 * 2 ^ 59
def prefixEnd_820423 : Nat := 4983230072969 + 3 ^ 40 * 820423 * 2
def baseEnd_820423 : Nat := 421271339003748824939449

theorem tailTrace_820423 : CollatzResearch.WordTrace tailWord_820423 prefixEnd_820423 421271339003748824939449 := by
  unfold tailWord_820423
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923285106755062938217923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19948856737836708625478615 29923285106755062938217923)
  ·
    refine ⟨44884927660132594407326885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29923285106755062938217923 44884927660132594407326885)
    ·
      refine ⟨8415923936274861451373791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44884927660132594407326885 8415923936274861451373791)
      ·
        refine ⟨12623885904412292177060687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415923936274861451373791 12623885904412292177060687)
        ·
          refine ⟨18935828856618438265591031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623885904412292177060687 18935828856618438265591031)
          ·
            refine ⟨28403743284927657398386547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18935828856618438265591031 28403743284927657398386547)
            ·
              refine ⟨42605614927391486097579821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28403743284927657398386547 42605614927391486097579821)
              ·
                refine ⟨15977105597771807286592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42605614927391486097579821 15977105597771807286592433)
                ·
                  refine ⟨11982829198328855464944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15977105597771807286592433 11982829198328855464944325)
                  ·
                    refine ⟨2246780474686660399677061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11982829198328855464944325 2246780474686660399677061)
                    ·
                      refine ⟨421271339003748824939449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2246780474686660399677061 421271339003748824939449)
                      ·
                        rfl

theorem cell23_820423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_820423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820423 prefixEnd_820423 := by exact prefixLift 820423
  have htrace : WordTrace (prefixWord ++ tailWord_820423) baseStart_820423 baseEnd_820423 := by
    simpa [prefixWord, tailWord_820423, baseEnd_820423] using wordTrace_append hprefix tailTrace_820423
  have hstable : (prefixWord ++ tailWord_820423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820423).length < 2 ^ (prefixWord ++ tailWord_820423).sum := by decide
  have hdescent : baseEnd_820423 < baseStart_820423 := by decide
  rcases family_descends (prefixWord ++ tailWord_820423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820473 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_820473 : Nat := 118140960795 + 820473 * 2 ^ 59
def prefixEnd_820473 : Nat := 4983230072969 + 3 ^ 40 * 820473 * 2
def baseEnd_820473 : Nat := 421297013036473629314219

theorem tailTrace_820473 : CollatzResearch.WordTrace tailWord_820473 prefixEnd_820473 421297013036473629314219 := by
  unfold tailWord_820473
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925108756573921477538073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19950072504382614318358715 29925108756573921477538073)
  ·
    refine ⟨22443831567430441108153555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29925108756573921477538073 22443831567430441108153555)
    ·
      refine ⟨33665747351145661662230333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22443831567430441108153555 33665747351145661662230333)
      ·
        refine ⟨12624655256679623123336375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33665747351145661662230333 12624655256679623123336375)
        ·
          refine ⟨18936982885019434685004563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12624655256679623123336375 18936982885019434685004563)
          ·
            refine ⟨28405474327529152027506845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18936982885019434685004563 28405474327529152027506845)
            ·
              refine ⟨10652052872823432010315067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28405474327529152027506845 10652052872823432010315067)
              ·
                refine ⟨15978079309235148015472601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652052872823432010315067 15978079309235148015472601)
                ·
                  refine ⟨11983559481926361011604451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15978079309235148015472601 11983559481926361011604451)
                  ·
                    refine ⟨17975339222889541517406677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11983559481926361011604451 17975339222889541517406677)
                    ·
                      refine ⟨421297013036473629314219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17975339222889541517406677 421297013036473629314219)
                      ·
                        rfl

theorem cell23_820473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_820473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820473 prefixEnd_820473 := by exact prefixLift 820473
  have htrace : WordTrace (prefixWord ++ tailWord_820473) baseStart_820473 baseEnd_820473 := by
    simpa [prefixWord, tailWord_820473, baseEnd_820473] using wordTrace_append hprefix tailTrace_820473
  have hstable : (prefixWord ++ tailWord_820473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820473).length < 2 ^ (prefixWord ++ tailWord_820473).sum := by decide
  have hdescent : baseEnd_820473 < baseStart_820473 := by decide
  rcases family_descends (prefixWord ++ tailWord_820473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820480 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_820480 : Nat := 118140960795 + 820480 * 2 ^ 59
def prefixEnd_820480 : Nat := 4983230072969 + 3 ^ 40 * 820480 * 2
def baseEnd_820480 : Nat := 140433535800351700642229

theorem tailTrace_820480 : CollatzResearch.WordTrace tailWord_820480 prefixEnd_820480 140433535800351700642229 := by
  unfold tailWord_820480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962682033774280836521447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19950242711699041115361929 14962682033774280836521447)
  ·
    refine ⟨22444023050661421254782171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14962682033774280836521447 22444023050661421254782171)
    ·
      refine ⟨33666034575992131882173257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22444023050661421254782171 33666034575992131882173257)
      ·
        refine ⟨25249525931994098911629943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33666034575992131882173257 25249525931994098911629943)
        ·
          refine ⟨37874288897991148367444915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25249525931994098911629943 37874288897991148367444915)
          ·
            refine ⟨56811433346986722551167373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37874288897991148367444915 56811433346986722551167373)
            ·
              refine ⟨21304287505120020956687765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56811433346986722551167373 21304287505120020956687765)
              ·
                refine ⟨998638476802500982344739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21304287505120020956687765 998638476802500982344739)
                ·
                  refine ⟨1497957715203751473517109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998638476802500982344739 1497957715203751473517109)
                  ·
                    refine ⟨140433535800351700642229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1497957715203751473517109 140433535800351700642229)
                    ·
                      rfl

theorem cell23_820480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_820480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820480 prefixEnd_820480 := by exact prefixLift 820480
  have htrace : WordTrace (prefixWord ++ tailWord_820480) baseStart_820480 baseEnd_820480 := by
    simpa [prefixWord, tailWord_820480, baseEnd_820480] using wordTrace_append hprefix tailTrace_820480
  have hstable : (prefixWord ++ tailWord_820480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820480).length < 2 ^ (prefixWord ++ tailWord_820480).sum := by decide
  have hdescent : baseEnd_820480 < baseStart_820480 := by decide
  rcases family_descends (prefixWord ++ tailWord_820480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820540 : List Nat := [2, 2, 2, 2, 1, 4, 1, 9]
def baseStart_820540 : Nat := 118140960795 + 820540 * 2 ^ 59
def prefixEnd_820540 : Nat := 4983230072969 + 3 ^ 40 * 820540 * 2
def baseEnd_820540 : Nat := 15604867268160180265793

theorem tailTrace_820540 : CollatzResearch.WordTrace tailWord_820540 prefixEnd_820540 15604867268160180265793 := by
  unfold tailWord_820540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14963776223665595960113537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19951701631554127946818049 14963776223665595960113537)
  ·
    refine ⟨11222832167749196970085153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14963776223665595960113537 11222832167749196970085153)
    ·
      refine ⟨8417124125811897727563865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11222832167749196970085153 8417124125811897727563865)
      ·
        refine ⟨6312843094358923295672899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8417124125811897727563865 6312843094358923295672899)
        ·
          refine ⟨9469264641538384943509349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312843094358923295672899 9469264641538384943509349)
          ·
            refine ⟨1775487120288447176908003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9469264641538384943509349 1775487120288447176908003)
            ·
              refine ⟨2663230680432670765362005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775487120288447176908003 2663230680432670765362005)
              ·
                refine ⟨15604867268160180265793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2663230680432670765362005 15604867268160180265793)
                ·
                  rfl

theorem cell23_820540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 9].length) (baseStart_820540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820540 prefixEnd_820540 := by exact prefixLift 820540
  have htrace : WordTrace (prefixWord ++ tailWord_820540) baseStart_820540 baseEnd_820540 := by
    simpa [prefixWord, tailWord_820540, baseEnd_820540] using wordTrace_append hprefix tailTrace_820540
  have hstable : (prefixWord ++ tailWord_820540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820540).length < 2 ^ (prefixWord ++ tailWord_820540).sum := by decide
  have hdescent : baseEnd_820540 < baseStart_820540 := by decide
  rcases family_descends (prefixWord ++ tailWord_820540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820568 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_820568 : Nat := 118140960795 + 820568 * 2 ^ 59
def prefixEnd_820568 : Nat := 4983230072969 + 3 ^ 40 * 820568 * 2
def baseEnd_820568 : Nat := 421345793698650757626283

theorem tailTrace_820568 : CollatzResearch.WordTrace tailWord_820568 prefixEnd_820568 421345793698650757626283 := by
  unfold tailWord_820568
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964286845614876351123179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19952382460819835134830905 14964286845614876351123179)
  ·
    refine ⟨22446430268422314526684769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964286845614876351123179 22446430268422314526684769)
    ·
      refine ⟨16834822701316735895013577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22446430268422314526684769 16834822701316735895013577)
      ·
        refine ⟨12626117025987551921260183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16834822701316735895013577 12626117025987551921260183)
        ·
          refine ⟨18939175538981327881890275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626117025987551921260183 18939175538981327881890275)
          ·
            refine ⟨28408763308471991822835413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18939175538981327881890275 28408763308471991822835413)
            ·
              refine ⟨665830390042312308347705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28408763308471991822835413 665830390042312308347705)
              ·
                refine ⟨499372792531734231260779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665830390042312308347705 499372792531734231260779)
                ·
                  refine ⟨749059188797601346891169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499372792531734231260779 749059188797601346891169)
                  ·
                    refine ⟨561794391598201010168377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 749059188797601346891169 561794391598201010168377)
                    ·
                      refine ⟨421345793698650757626283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561794391598201010168377 421345793698650757626283)
                      ·
                        rfl

theorem cell23_820568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_820568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820568 prefixEnd_820568 := by exact prefixLift 820568
  have htrace : WordTrace (prefixWord ++ tailWord_820568) baseStart_820568 baseEnd_820568 := by
    simpa [prefixWord, tailWord_820568, baseEnd_820568] using wordTrace_append hprefix tailTrace_820568
  have hstable : (prefixWord ++ tailWord_820568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820568).length < 2 ^ (prefixWord ++ tailWord_820568).sum := by decide
  have hdescent : baseEnd_820568 < baseStart_820568 := by decide
  rcases family_descends (prefixWord ++ tailWord_820568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820594 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_820594 : Nat := 118140960795 + 820594 * 2 ^ 59
def prefixEnd_820594 : Nat := 4983230072969 + 3 ^ 40 * 820594 * 2
def baseEnd_820594 : Nat := 421359144195667655901163

theorem tailTrace_820594 : CollatzResearch.WordTrace tailWord_820594 prefixEnd_820594 421359144195667655901163 := by
  unfold tailWord_820594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482380497283889785673209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19953014659423706095128557 7482380497283889785673209)
  ·
    refine ⟨5611785372962917339254907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7482380497283889785673209 5611785372962917339254907)
    ·
      refine ⟨8417678059444376008882361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5611785372962917339254907 8417678059444376008882361)
      ·
        refine ⟨6313258544583282006661771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8417678059444376008882361 6313258544583282006661771)
        ·
          refine ⟨9469887816874923009992657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313258544583282006661771 9469887816874923009992657)
          ·
            refine ⟨7102415862656192257494493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9469887816874923009992657 7102415862656192257494493)
            ·
              refine ⟨2663405948496072096560435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7102415862656192257494493 2663405948496072096560435)
              ·
                refine ⟨3995108922744108144840653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663405948496072096560435 3995108922744108144840653)
                ·
                  refine ⟨1498165846029040554315245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3995108922744108144840653 1498165846029040554315245)
                  ·
                    refine ⟨561812192260890207868217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498165846029040554315245 561812192260890207868217)
                    ·
                      refine ⟨421359144195667655901163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561812192260890207868217 421359144195667655901163)
                      ·
                        rfl

theorem cell23_820594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_820594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820594 prefixEnd_820594 := by exact prefixLift 820594
  have htrace : WordTrace (prefixWord ++ tailWord_820594) baseStart_820594 baseEnd_820594 := by
    simpa [prefixWord, tailWord_820594, baseEnd_820594] using wordTrace_append hprefix tailTrace_820594
  have hstable : (prefixWord ++ tailWord_820594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820594).length < 2 ^ (prefixWord ++ tailWord_820594).sum := by decide
  have hdescent : baseEnd_820594 < baseStart_820594 := by decide
  rcases family_descends (prefixWord ++ tailWord_820594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820637 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_820637 : Nat := 118140960795 + 820637 * 2 ^ 59
def prefixEnd_820637 : Nat := 4983230072969 + 3 ^ 40 * 820637 * 2
def baseEnd_820637 : Nat := 421381223863810987663465

theorem tailTrace_820637 : CollatzResearch.WordTrace tailWord_820637 prefixEnd_820637 421381223863810987663465 := by
  unfold tailWord_820637
  simp only [CollatzResearch.WordTrace]
  refine ⟨29931090327979777486508165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19954060218653184991005443 29931090327979777486508165)
  ·
    refine ⟨5612079436496208278720281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29931090327979777486508165 5612079436496208278720281)
    ·
      refine ⟨4209059577372156209040211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5612079436496208278720281 4209059577372156209040211)
      ·
        refine ⟨6313589366058234313560317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209059577372156209040211 6313589366058234313560317)
        ·
          refine ⟨2367596012271837867585119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6313589366058234313560317 2367596012271837867585119)
          ·
            refine ⟨3551394018407756801377679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367596012271837867585119 3551394018407756801377679)
            ·
              refine ⟨5327091027611635202066519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551394018407756801377679 5327091027611635202066519)
              ·
                refine ⟨7990636541417452803099779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327091027611635202066519 7990636541417452803099779)
                ·
                  refine ⟨11985954812126179204649669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990636541417452803099779 11985954812126179204649669)
                  ·
                    refine ⟨2247366527273658600871813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11985954812126179204649669 2247366527273658600871813)
                    ·
                      refine ⟨421381223863810987663465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2247366527273658600871813 421381223863810987663465)
                      ·
                        rfl

theorem cell23_820637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_820637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820637 prefixEnd_820637 := by exact prefixLift 820637
  have htrace : WordTrace (prefixWord ++ tailWord_820637) baseStart_820637 baseEnd_820637 := by
    simpa [prefixWord, tailWord_820637, baseEnd_820637] using wordTrace_append hprefix tailTrace_820637
  have hstable : (prefixWord ++ tailWord_820637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820637).length < 2 ^ (prefixWord ++ tailWord_820637).sum := by decide
  have hdescent : baseEnd_820637 < baseStart_820637 := by decide
  rcases family_descends (prefixWord ++ tailWord_820637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820647 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 7]
def baseStart_820647 : Nat := 118140960795 + 820647 * 2 ^ 59
def prefixEnd_820647 : Nat := 4983230072969 + 3 ^ 40 * 820647 * 2
def baseEnd_820647 : Nat := 46820706518928438726491

theorem tailTrace_820647 : CollatzResearch.WordTrace tailWord_820647 prefixEnd_820647 46820706518928438726491 := by
  unfold tailWord_820647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29931455057943549194372195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19954303371962366129581463 29931455057943549194372195)
  ·
    refine ⟨44897182586915323791558293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29931455057943549194372195 44897182586915323791558293)
    ·
      refine ⟨2104555433761655802729295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44897182586915323791558293 2104555433761655802729295)
      ·
        refine ⟨3156833150642483704093943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104555433761655802729295 3156833150642483704093943)
        ·
          refine ⟨4735249725963725556140915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156833150642483704093943 4735249725963725556140915)
          ·
            refine ⟨7102874588945588334211373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735249725963725556140915 7102874588945588334211373)
            ·
              refine ⟨2663577970854595625329265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7102874588945588334211373 2663577970854595625329265)
              ·
                refine ⟨1997683478140946718996949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663577970854595625329265 1997683478140946718996949)
                ·
                  refine ⟨46820706518928438726491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1997683478140946718996949 46820706518928438726491)
                  ·
                    rfl

theorem cell23_820647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 7].length) (baseStart_820647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820647 prefixEnd_820647 := by exact prefixLift 820647
  have htrace : WordTrace (prefixWord ++ tailWord_820647) baseStart_820647 baseEnd_820647 := by
    simpa [prefixWord, tailWord_820647, baseEnd_820647] using wordTrace_append hprefix tailTrace_820647
  have hstable : (prefixWord ++ tailWord_820647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820647).length < 2 ^ (prefixWord ++ tailWord_820647).sum := by decide
  have hdescent : baseEnd_820647 < baseStart_820647 := by decide
  rcases family_descends (prefixWord ++ tailWord_820647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820657 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_820657 : Nat := 118140960795 + 820657 * 2 ^ 59
def prefixEnd_820657 : Nat := 4983230072969 + 3 ^ 40 * 820657 * 2
def baseEnd_820657 : Nat := 421391493476900909413373

theorem tailTrace_820657 : CollatzResearch.WordTrace tailWord_820657 prefixEnd_820657 421391493476900909413373 := by
  unfold tailWord_820657
  simp only [CollatzResearch.WordTrace]
  refine ⟨29931819787907320902236225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19954546525271547268157483 29931819787907320902236225)
  ·
    refine ⟨22448864840930490676677169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29931819787907320902236225 22448864840930490676677169)
    ·
      refine ⟨16836648630697868007507877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22448864840930490676677169 16836648630697868007507877)
      ·
        refine ⟨3156871618255850251407727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16836648630697868007507877 3156871618255850251407727)
        ·
          refine ⟨4735307427383775377111591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156871618255850251407727 4735307427383775377111591)
          ·
            refine ⟨7102961141075663065667387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735307427383775377111591 7102961141075663065667387)
            ·
              refine ⟨10654441711613494598501081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102961141075663065667387 10654441711613494598501081)
              ·
                refine ⟨7990831283710120948875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10654441711613494598501081 7990831283710120948875811)
                ·
                  refine ⟨11986246925565181423313717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990831283710120948875811 11986246925565181423313717)
                  ·
                    refine ⟨1123710649271735758435661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11986246925565181423313717 1123710649271735758435661)
                    ·
                      refine ⟨421391493476900909413373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1123710649271735758435661 421391493476900909413373)
                      ·
                        rfl

theorem cell23_820657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_820657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820657 prefixEnd_820657 := by exact prefixLift 820657
  have htrace : WordTrace (prefixWord ++ tailWord_820657) baseStart_820657 baseEnd_820657 := by
    simpa [prefixWord, tailWord_820657, baseEnd_820657] using wordTrace_append hprefix tailTrace_820657
  have hstable : (prefixWord ++ tailWord_820657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820657).length < 2 ^ (prefixWord ++ tailWord_820657).sum := by decide
  have hdescent : baseEnd_820657 < baseStart_820657 := by decide
  rcases family_descends (prefixWord ++ tailWord_820657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820694 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_820694 : Nat := 118140960795 + 820694 * 2 ^ 59
def prefixEnd_820694 : Nat := 4983230072969 + 3 ^ 40 * 820694 * 2
def baseEnd_820694 : Nat := 140470164087039088216901

theorem tailTrace_820694 : CollatzResearch.WordTrace tailWord_820694 prefixEnd_820694 140470164087039088216901 := by
  unfold tailWord_820694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870823080548329763833321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19955446192515517480888757 1870823080548329763833321)
  ·
    refine ⟨1403117310411247322874991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1870823080548329763833321 1403117310411247322874991)
    ·
      refine ⟨2104675965616870984312487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403117310411247322874991 2104675965616870984312487)
      ·
        refine ⟨3157013948425306476468731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104675965616870984312487 3157013948425306476468731)
        ·
          refine ⟨4735520922637959714703097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157013948425306476468731 4735520922637959714703097)
          ·
            refine ⟨3551640691978469786027323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735520922637959714703097 3551640691978469786027323)
            ·
              refine ⟨5327461037967704679040985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551640691978469786027323 5327461037967704679040985)
              ·
                refine ⟨3995595778475778509280739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327461037967704679040985 3995595778475778509280739)
                ·
                  refine ⟨5993393667713667763921109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995595778475778509280739 5993393667713667763921109)
                  ·
                    refine ⟨140470164087039088216901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5993393667713667763921109 140470164087039088216901)
                    ·
                      rfl

theorem cell23_820694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_820694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820694 prefixEnd_820694 := by exact prefixLift 820694
  have htrace : WordTrace (prefixWord ++ tailWord_820694) baseStart_820694 baseEnd_820694 := by
    simpa [prefixWord, tailWord_820694, baseEnd_820694] using wordTrace_append hprefix tailTrace_820694
  have hstable : (prefixWord ++ tailWord_820694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820694).length < 2 ^ (prefixWord ++ tailWord_820694).sum := by decide
  have hdescent : baseEnd_820694 < baseStart_820694 := by decide
  rcases family_descends (prefixWord ++ tailWord_820694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820697 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_820697 : Nat := 118140960795 + 820697 * 2 ^ 59
def prefixEnd_820697 : Nat := 4983230072969 + 3 ^ 40 * 820697 * 2
def baseEnd_820697 : Nat := 421412032703080752913189

theorem tailTrace_820697 : CollatzResearch.WordTrace tailWord_820697 prefixEnd_820697 421412032703080752913189 := by
  unfold tailWord_820697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933278707762407733692345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19955519138508271822461563 29933278707762407733692345)
  ·
    refine ⟨22449959030821805800269259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29933278707762407733692345 22449959030821805800269259)
    ·
      refine ⟨33674938546232708700403889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22449959030821805800269259 33674938546232708700403889)
      ·
        refine ⟨25256203909674531525302917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33674938546232708700403889 25256203909674531525302917)
        ·
          refine ⟨4735538233063974660994297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25256203909674531525302917 4735538233063974660994297)
          ·
            refine ⟨3551653674797980995745723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735538233063974660994297 3551653674797980995745723)
            ·
              refine ⟨5327480512196971493618585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551653674797980995745723 5327480512196971493618585)
              ·
                refine ⟨3995610384147728620213939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327480512196971493618585 3995610384147728620213939)
                ·
                  refine ⟨5993415576221592930320909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995610384147728620213939 5993415576221592930320909)
                  ·
                    refine ⟨2247530841083097348870341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5993415576221592930320909 2247530841083097348870341)
                    ·
                      refine ⟨421412032703080752913189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2247530841083097348870341 421412032703080752913189)
                      ·
                        rfl

theorem cell23_820697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_820697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820697 prefixEnd_820697 := by exact prefixLift 820697
  have htrace : WordTrace (prefixWord ++ tailWord_820697) baseStart_820697 baseEnd_820697 := by
    simpa [prefixWord, tailWord_820697, baseEnd_820697] using wordTrace_append hprefix tailTrace_820697
  have hstable : (prefixWord ++ tailWord_820697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820697).length < 2 ^ (prefixWord ++ tailWord_820697).sum := by decide
  have hdescent : baseEnd_820697 < baseStart_820697 := by decide
  rcases family_descends (prefixWord ++ tailWord_820697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820791 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_820791 : Nat := 118140960795 + 820791 * 2 ^ 59
def prefixEnd_820791 : Nat := 4983230072969 + 3 ^ 40 * 820791 * 2
def baseEnd_820791 : Nat := 421460299884603385137757

theorem tailTrace_820791 : CollatzResearch.WordTrace tailWord_820791 prefixEnd_820791 421460299884603385137757 := by
  unfold tailWord_820791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29936707169421861787614227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19957804779614574525076151 29936707169421861787614227)
  ·
    refine ⟨44905060754132792681421341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29936707169421861787614227 44905060754132792681421341)
    ·
      refine ⟨16839397782799797255533003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44905060754132792681421341 16839397782799797255533003)
      ·
        refine ⟨25259096674199695883299505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16839397782799797255533003 25259096674199695883299505)
        ·
          refine ⟨18944322505649771912474629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25259096674199695883299505 18944322505649771912474629)
          ·
            refine ⟨3552060469809332233588993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18944322505649771912474629 3552060469809332233588993)
            ·
              refine ⟨2664045352356999175191745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552060469809332233588993 2664045352356999175191745)
              ·
                refine ⟨1998034014267749381393809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664045352356999175191745 1998034014267749381393809)
                ·
                  refine ⟨1498525510700812036045357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998034014267749381393809 1498525510700812036045357)
                  ·
                    refine ⟨561947066512804513517009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498525510700812036045357 561947066512804513517009)
                    ·
                      refine ⟨421460299884603385137757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 561947066512804513517009 421460299884603385137757)
                      ·
                        rfl

theorem cell23_820791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_820791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820791 prefixEnd_820791 := by exact prefixLift 820791
  have htrace : WordTrace (prefixWord ++ tailWord_820791) baseStart_820791 baseEnd_820791 := by
    simpa [prefixWord, tailWord_820791, baseEnd_820791] using wordTrace_append hprefix tailTrace_820791
  have hstable : (prefixWord ++ tailWord_820791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820791).length < 2 ^ (prefixWord ++ tailWord_820791).sum := by decide
  have hdescent : baseEnd_820791 < baseStart_820791 := by decide
  rcases family_descends (prefixWord ++ tailWord_820791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820814 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_820814 : Nat := 118140960795 + 820814 * 2 ^ 59
def prefixEnd_820814 : Nat := 4983230072969 + 3 ^ 40 * 820814 * 2
def baseEnd_820814 : Nat := 140490703313218931716717

theorem tailTrace_820814 : CollatzResearch.WordTrace tailWord_820814 prefixEnd_820814 140490703313218931716717 := by
  unfold tailWord_820814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742193256042317089462687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19958364032225691143800997 3742193256042317089462687)
  ·
    refine ⟨5613289884063475634194031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3742193256042317089462687 5613289884063475634194031)
    ·
      refine ⟨8419934826095213451291047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613289884063475634194031 8419934826095213451291047)
      ·
        refine ⟨12629902239142820176936571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419934826095213451291047 12629902239142820176936571)
        ·
          refine ⟨18944853358714230265404857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12629902239142820176936571 18944853358714230265404857)
          ·
            refine ⟨14208640019035672699053643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18944853358714230265404857 14208640019035672699053643)
            ·
              refine ⟨21312960028553509048580465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208640019035672699053643 21312960028553509048580465)
              ·
                refine ⟨15984720021415131786435349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312960028553509048580465 15984720021415131786435349)
                ·
                  refine ⟨749283751003834302489157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15984720021415131786435349 749283751003834302489157)
                  ·
                    refine ⟨140490703313218931716717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749283751003834302489157 140490703313218931716717)
                    ·
                      rfl

theorem cell23_820814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_820814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820814 prefixEnd_820814 := by exact prefixLift 820814
  have htrace : WordTrace (prefixWord ++ tailWord_820814) baseStart_820814 baseEnd_820814 := by
    simpa [prefixWord, tailWord_820814, baseEnd_820814] using wordTrace_append hprefix tailTrace_820814
  have hstable : (prefixWord ++ tailWord_820814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820814).length < 2 ^ (prefixWord ++ tailWord_820814).sum := by decide
  have hdescent : baseEnd_820814 < baseStart_820814 := by decide
  rcases family_descends (prefixWord ++ tailWord_820814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_820847 : Nat := 118140960795 + 820847 * 2 ^ 59
def prefixEnd_820847 : Nat := 4983230072969 + 3 ^ 40 * 820847 * 2
def baseEnd_820847 : Nat := 421489054801255166037499

theorem tailTrace_820847 : CollatzResearch.WordTrace tailWord_820847 prefixEnd_820847 421489054801255166037499 := by
  unfold tailWord_820847
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938749657218983351652795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19959166438145988901101863 29938749657218983351652795)
  ·
    refine ⟨44908124485828475027479193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29938749657218983351652795 44908124485828475027479193)
    ·
      refine ⟨33681093364371356270609395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44908124485828475027479193 33681093364371356270609395)
      ·
        refine ⟨50521640046557034405914093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33681093364371356270609395 50521640046557034405914093)
        ·
          refine ⟨18945615017458887902217785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50521640046557034405914093 18945615017458887902217785)
          ·
            refine ⟨14209211263094165926663339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18945615017458887902217785 14209211263094165926663339)
            ·
              refine ⟨21313816894641248889995009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14209211263094165926663339 21313816894641248889995009)
              ·
                refine ⟨15985362670980936667496257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21313816894641248889995009 15985362670980936667496257)
                ·
                  refine ⟨11989022003235702500622193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15985362670980936667496257 11989022003235702500622193)
                  ·
                    refine ⟨8991766502426776875466645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11989022003235702500622193 8991766502426776875466645)
                    ·
                      refine ⟨421489054801255166037499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8991766502426776875466645 421489054801255166037499)
                      ·
                        rfl

theorem cell23_820847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_820847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820847 prefixEnd_820847 := by exact prefixLift 820847
  have htrace : WordTrace (prefixWord ++ tailWord_820847) baseStart_820847 baseEnd_820847 := by
    simpa [prefixWord, tailWord_820847, baseEnd_820847] using wordTrace_append hprefix tailTrace_820847
  have hstable : (prefixWord ++ tailWord_820847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820847).length < 2 ^ (prefixWord ++ tailWord_820847).sum := by decide
  have hdescent : baseEnd_820847 < baseStart_820847 := by decide
  rcases family_descends (prefixWord ++ tailWord_820847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820848 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_820848 : Nat := 118140960795 + 820848 * 2 ^ 59
def prefixEnd_820848 : Nat := 4983230072969 + 3 ^ 40 * 820848 * 2
def baseEnd_820848 : Nat := 140496522760636554041665

theorem tailTrace_820848 : CollatzResearch.WordTrace tailWord_820848 prefixEnd_820848 140496522760636554041665 := by
  unfold tailWord_820848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969393065107680261219599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19959190753476907014959465 14969393065107680261219599)
  ·
    refine ⟨22454089597661520391829399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14969393065107680261219599 22454089597661520391829399)
    ·
      refine ⟨33681134396492280587744099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22454089597661520391829399 33681134396492280587744099)
      ·
        refine ⟨50521701594738420881616149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33681134396492280587744099 50521701594738420881616149)
        ·
          refine ⟨2368204762253363478825757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50521701594738420881616149 2368204762253363478825757)
          ·
            refine ⟨888076785845011304559659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2368204762253363478825757 888076785845011304559659)
            ·
              refine ⟨1332115178767516956839489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888076785845011304559659 1332115178767516956839489)
              ·
                refine ⟨999086384075637717629617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332115178767516956839489 999086384075637717629617)
                ·
                  refine ⟨749314788056728288222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999086384075637717629617 749314788056728288222213)
                  ·
                    refine ⟨140496522760636554041665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749314788056728288222213 140496522760636554041665)
                    ·
                      rfl

theorem cell23_820848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_820848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820848 prefixEnd_820848 := by exact prefixLift 820848
  have htrace : WordTrace (prefixWord ++ tailWord_820848) baseStart_820848 baseEnd_820848 := by
    simpa [prefixWord, tailWord_820848, baseEnd_820848] using wordTrace_append hprefix tailTrace_820848
  have hstable : (prefixWord ++ tailWord_820848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820848).length < 2 ^ (prefixWord ++ tailWord_820848).sum := by decide
  have hdescent : baseEnd_820848 < baseStart_820848 := by decide
  rcases family_descends (prefixWord ++ tailWord_820848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820868 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_820868 : Nat := 118140960795 + 820868 * 2 ^ 59
def prefixEnd_820868 : Nat := 4983230072969 + 3 ^ 40 * 820868 * 2
def baseEnd_820868 : Nat := 421499837894999583874903

theorem tailTrace_820868 : CollatzResearch.WordTrace tailWord_820868 prefixEnd_820868 421499837894999583874903 := by
  unfold tailWord_820868
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969757795071451969083629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19959677060095269292111505 14969757795071451969083629)
  ·
    refine ⟨5613659173151794488406361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14969757795071451969083629 5613659173151794488406361)
    ·
      refine ⟨4210244379863845866304771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613659173151794488406361 4210244379863845866304771)
      ·
        refine ⟨6315366569795768799457157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210244379863845866304771 6315366569795768799457157)
        ·
          refine ⟨1184131231836706649898217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6315366569795768799457157 1184131231836706649898217)
          ·
            refine ⟨888098423877529987423663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184131231836706649898217 888098423877529987423663)
            ·
              refine ⟨1332147635816294981135495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888098423877529987423663 1332147635816294981135495)
              ·
                refine ⟨1998221453724442471703243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332147635816294981135495 1998221453724442471703243)
                ·
                  refine ⟨2997332180586663707554865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998221453724442471703243 2997332180586663707554865)
                  ·
                    refine ⟨2247999135439997780666149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997332180586663707554865 2247999135439997780666149)
                    ·
                      refine ⟨421499837894999583874903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2247999135439997780666149 421499837894999583874903)
                      ·
                        rfl

theorem cell23_820868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_820868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820868 prefixEnd_820868 := by exact prefixLift 820868
  have htrace : WordTrace (prefixWord ++ tailWord_820868) baseStart_820868 baseEnd_820868 := by
    simpa [prefixWord, tailWord_820868, baseEnd_820868] using wordTrace_append hprefix tailTrace_820868
  have hstable : (prefixWord ++ tailWord_820868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820868).length < 2 ^ (prefixWord ++ tailWord_820868).sum := by decide
  have hdescent : baseEnd_820868 < baseStart_820868 := by decide
  rcases family_descends (prefixWord ++ tailWord_820868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820871 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_820871 : Nat := 118140960795 + 820871 * 2 ^ 59
def prefixEnd_820871 : Nat := 4983230072969 + 3 ^ 40 * 820871 * 2
def baseEnd_820871 : Nat := 421501378336963072137389

theorem tailTrace_820871 : CollatzResearch.WordTrace tailWord_820871 prefixEnd_820871 421501378336963072137389 := by
  unfold tailWord_820871
  simp only [CollatzResearch.WordTrace]
  refine ⟨29939625009132035450526467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19959750006088023633684311 29939625009132035450526467)
  ·
    refine ⟨44909437513698053175789701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29939625009132035450526467 44909437513698053175789701)
    ·
      refine ⟨8420519533818384970460569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44909437513698053175789701 8420519533818384970460569)
      ·
        refine ⟨6315389650363788727845427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8420519533818384970460569 6315389650363788727845427)
        ·
          refine ⟨9473084475545683091768141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315389650363788727845427 9473084475545683091768141)
          ·
            refine ⟨3552406678329631159413053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9473084475545683091768141 3552406678329631159413053)
            ·
              refine ⟨1332152504373611684779895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3552406678329631159413053 1332152504373611684779895)
              ·
                refine ⟨1998228756560417527169843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332152504373611684779895 1998228756560417527169843)
                ·
                  refine ⟨2997343134840626290754765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998228756560417527169843 2997343134840626290754765)
                  ·
                    refine ⟨1124003675565234859033037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997343134840626290754765 1124003675565234859033037)
                    ·
                      refine ⟨421501378336963072137389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124003675565234859033037 421501378336963072137389)
                      ·
                        rfl

theorem cell23_820871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_820871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820871 prefixEnd_820871 := by exact prefixLift 820871
  have htrace : WordTrace (prefixWord ++ tailWord_820871) baseStart_820871 baseEnd_820871 := by
    simpa [prefixWord, tailWord_820871, baseEnd_820871] using wordTrace_append hprefix tailTrace_820871
  have hstable : (prefixWord ++ tailWord_820871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820871).length < 2 ^ (prefixWord ++ tailWord_820871).sum := by decide
  have hdescent : baseEnd_820871 < baseStart_820871 := by decide
  rcases family_descends (prefixWord ++ tailWord_820871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820944 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_820944 : Nat := 118140960795 + 820944 * 2 ^ 59
def prefixEnd_820944 : Nat := 4983230072969 + 3 ^ 40 * 820944 * 2
def baseEnd_820944 : Nat := 421538862424741286524553

theorem tailTrace_820944 : CollatzResearch.WordTrace tailWord_820944 prefixEnd_820944 421538862424741286524553 := by
  unfold tailWord_820944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14971143768933784458966943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19961525025245045945289257 14971143768933784458966943)
  ·
    refine ⟨22456715653400676688450415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14971143768933784458966943 22456715653400676688450415)
    ·
      refine ⟨33685073480101015032675623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22456715653400676688450415 33685073480101015032675623)
      ·
        refine ⟨50527610220151522549013435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33685073480101015032675623 50527610220151522549013435)
        ·
          refine ⟨75791415330227283823520153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50527610220151522549013435 75791415330227283823520153)
          ·
            refine ⟨56843561497670462867640115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75791415330227283823520153 56843561497670462867640115)
            ·
              refine ⟨85265342246505694301460173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56843561497670462867640115 85265342246505694301460173)
              ·
                refine ⟨31974503342439635363047565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85265342246505694301460173 31974503342439635363047565)
                ·
                  refine ⟨11990438753414863261142837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31974503342439635363047565 11990438753414863261142837)
                  ·
                    refine ⟨1124103633132643430732141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11990438753414863261142837 1124103633132643430732141)
                    ·
                      refine ⟨421538862424741286524553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124103633132643430732141 421538862424741286524553)
                      ·
                        rfl

theorem cell23_820944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_820944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820944 prefixEnd_820944 := by exact prefixLift 820944
  have htrace : WordTrace (prefixWord ++ tailWord_820944) baseStart_820944 baseEnd_820944 := by
    simpa [prefixWord, tailWord_820944, baseEnd_820944] using wordTrace_append hprefix tailTrace_820944
  have hstable : (prefixWord ++ tailWord_820944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820944).length < 2 ^ (prefixWord ++ tailWord_820944).sum := by decide
  have hdescent : baseEnd_820944 < baseStart_820944 := by decide
  rcases family_descends (prefixWord ++ tailWord_820944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820951 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 5]
def baseStart_820951 : Nat := 118140960795 + 820951 * 2 ^ 59
def prefixEnd_820951 : Nat := 4983230072969 + 3 ^ 40 * 820951 * 2
def baseEnd_820951 : Nat := 46838050754369195459669

theorem tailTrace_820951 : CollatzResearch.WordTrace tailWord_820951 prefixEnd_820951 46838050754369195459669 := by
  unfold tailWord_820951
  simp only [CollatzResearch.WordTrace]
  refine ⟨29942542848842209113438707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19961695232561472742292471 29942542848842209113438707)
  ·
    refine ⟨44913814273263313670158061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29942542848842209113438707 44913814273263313670158061)
    ·
      refine ⟨16842680352473742626309273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44913814273263313670158061 16842680352473742626309273)
      ·
        refine ⟨12632010264355306969731955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16842680352473742626309273 12632010264355306969731955)
        ·
          refine ⟨18948015396532960454597933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632010264355306969731955 18948015396532960454597933)
          ·
            refine ⟨7105505773699860170474225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18948015396532960454597933 7105505773699860170474225)
            ·
              refine ⟨5329129330274895127855669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105505773699860170474225 5329129330274895127855669)
              ·
                refine ⟨499605874713271418236469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5329129330274895127855669 499605874713271418236469)
                ·
                  refine ⟨46838050754369195459669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499605874713271418236469 46838050754369195459669)
                  ·
                    rfl

theorem cell23_820951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 5].length) (baseStart_820951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820951 prefixEnd_820951 := by exact prefixLift 820951
  have htrace : WordTrace (prefixWord ++ tailWord_820951) baseStart_820951 baseEnd_820951 := by
    simpa [prefixWord, tailWord_820951, baseEnd_820951] using wordTrace_append hprefix tailTrace_820951
  have hstable : (prefixWord ++ tailWord_820951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820951).length < 2 ^ (prefixWord ++ tailWord_820951).sum := by decide
  have hdescent : baseEnd_820951 < baseStart_820951 := by decide
  rcases family_descends (prefixWord ++ tailWord_820951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820968 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 5]
def baseStart_820968 : Nat := 118140960795 + 820968 * 2 ^ 59
def prefixEnd_820968 : Nat := 4983230072969 + 3 ^ 40 * 820968 * 2
def baseEnd_820968 : Nat := 46839020662272132513827

theorem tailTrace_820968 : CollatzResearch.WordTrace tailWord_820968 prefixEnd_820968 46839020662272132513827 := by
  unfold tailWord_820968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14971581444890310508403779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19962108593187080677871705 14971581444890310508403779)
  ·
    refine ⟨22457372167335465762605669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14971581444890310508403779 22457372167335465762605669)
    ·
      refine ⟨4210757281375399830488563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22457372167335465762605669 4210757281375399830488563)
      ·
        refine ⟨6316135922063099745732845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210757281375399830488563 6316135922063099745732845)
        ·
          refine ⟨2368550970773662404649817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6316135922063099745732845 2368550970773662404649817)
          ·
            refine ⟨1776413228080246803487363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368550970773662404649817 1776413228080246803487363)
            ·
              refine ⟨2664619842120370205231045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776413228080246803487363 2664619842120370205231045)
              ·
                refine ⟨499616220397569413480821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2664619842120370205231045 499616220397569413480821)
                ·
                  refine ⟨46839020662272132513827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499616220397569413480821 46839020662272132513827)
                  ·
                    rfl

theorem cell23_820968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 5].length) (baseStart_820968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820968 prefixEnd_820968 := by exact prefixLift 820968
  have htrace : WordTrace (prefixWord ++ tailWord_820968) baseStart_820968 baseEnd_820968 := by
    simpa [prefixWord, tailWord_820968, baseEnd_820968] using wordTrace_append hprefix tailTrace_820968
  have hstable : (prefixWord ++ tailWord_820968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820968).length < 2 ^ (prefixWord ++ tailWord_820968).sum := by decide
  have hdescent : baseEnd_820968 < baseStart_820968 := by decide
  rcases family_descends (prefixWord ++ tailWord_820968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820971 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 5, 2]
def baseStart_820971 : Nat := 118140960795 + 820971 * 2 ^ 59
def prefixEnd_820971 : Nat := 4983230072969 + 3 ^ 40 * 820971 * 2
def baseEnd_820971 : Nat := 421552726402412680886929

theorem tailTrace_820971 : CollatzResearch.WordTrace tailWord_820971 prefixEnd_820971 421552726402412680886929 := by
  unfold tailWord_820971
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943272308769752529166767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19962181539179835019444511 29943272308769752529166767)
  ·
    refine ⟨44914908463154628793750151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29943272308769752529166767 44914908463154628793750151)
    ·
      refine ⟨67372362694731943190625227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44914908463154628793750151 67372362694731943190625227)
      ·
        refine ⟨101058544042097914785937841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67372362694731943190625227 101058544042097914785937841)
        ·
          refine ⟨75793908031573436089453381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101058544042097914785937841 75793908031573436089453381)
          ·
            refine ⟨14211357755920019266772509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75793908031573436089453381 14211357755920019266772509)
            ·
              refine ⟨5329259158470007225039691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14211357755920019266772509 5329259158470007225039691)
              ·
                refine ⟨7993888737705010837559537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329259158470007225039691 7993888737705010837559537)
                ·
                  refine ⟨5995416553278758128169653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993888737705010837559537 5995416553278758128169653)
                  ·
                    refine ⟨562070301869883574515905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5995416553278758128169653 562070301869883574515905)
                    ·
                      refine ⟨421552726402412680886929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562070301869883574515905 421552726402412680886929)
                      ·
                        rfl

theorem cell23_820971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5, 2].length) (baseStart_820971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_820971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_820971 prefixEnd_820971 := by exact prefixLift 820971
  have htrace : WordTrace (prefixWord ++ tailWord_820971) baseStart_820971 baseEnd_820971 := by
    simpa [prefixWord, tailWord_820971, baseEnd_820971] using wordTrace_append hprefix tailTrace_820971
  have hstable : (prefixWord ++ tailWord_820971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820971).length < 2 ^ (prefixWord ++ tailWord_820971).sum := by decide
  have hdescent : baseEnd_820971 < baseStart_820971 := by decide
  rcases family_descends (prefixWord ++ tailWord_820971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821001 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 6, 2]
def baseStart_821001 : Nat := 118140960795 + 821001 * 2 ^ 59
def prefixEnd_821001 : Nat := 4983230072969 + 3 ^ 40 * 821001 * 2
def baseEnd_821001 : Nat := 421568130822047563511791

theorem tailTrace_821001 : CollatzResearch.WordTrace tailWord_821001 prefixEnd_821001 421568130822047563511791 := by
  unfold tailWord_821001
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944366498661067652758857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19962910999107378435172571 29944366498661067652758857)
  ·
    refine ⟨22458274873995800739569143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29944366498661067652758857 22458274873995800739569143)
    ·
      refine ⟨33687412310993701109353715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22458274873995800739569143 33687412310993701109353715)
      ·
        refine ⟨50531118466490551664030573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33687412310993701109353715 50531118466490551664030573)
        ·
          refine ⟨18949169424933956874011465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50531118466490551664030573 18949169424933956874011465)
          ·
            refine ⟨14211877068700467655508599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18949169424933956874011465 14211877068700467655508599)
            ·
              refine ⟨21317815603050701483262899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211877068700467655508599 21317815603050701483262899)
              ·
                refine ⟨31976723404576052224894349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21317815603050701483262899 31976723404576052224894349)
                ·
                  refine ⟨11991271276716019584335381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31976723404576052224894349 11991271276716019584335381)
                  ·
                    refine ⟨562090841096063418015721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11991271276716019584335381 562090841096063418015721)
                    ·
                      refine ⟨421568130822047563511791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562090841096063418015721 421568130822047563511791)
                      ·
                        rfl

theorem cell23_821001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6, 2].length) (baseStart_821001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821001 prefixEnd_821001 := by exact prefixLift 821001
  have htrace : WordTrace (prefixWord ++ tailWord_821001) baseStart_821001 baseEnd_821001 := by
    simpa [prefixWord, tailWord_821001, baseEnd_821001] using wordTrace_append hprefix tailTrace_821001
  have hstable : (prefixWord ++ tailWord_821001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821001).length < 2 ^ (prefixWord ++ tailWord_821001).sum := by decide
  have hdescent : baseEnd_821001 < baseStart_821001 := by decide
  rcases family_descends (prefixWord ++ tailWord_821001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821018 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_821018 : Nat := 118140960795 + 821018 * 2 ^ 59
def prefixEnd_821018 : Nat := 4983230072969 + 3 ^ 40 * 821018 * 2
def baseEnd_821018 : Nat := 421576859993173996999213

theorem tailTrace_821018 : CollatzResearch.WordTrace tailWord_821018 prefixEnd_821018 421576859993173996999213 := by
  unfold tailWord_821018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486246634899869889031927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19963324359732986370751805 7486246634899869889031927)
  ·
    refine ⟨11229369952349804833547891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7486246634899869889031927 11229369952349804833547891)
    ·
      refine ⟨16844054928524707250321837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229369952349804833547891 16844054928524707250321837)
      ·
        refine ⟨6316520598196765218870689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16844054928524707250321837 6316520598196765218870689)
        ·
          refine ⟨4737390448647573914153017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6316520598196765218870689 4737390448647573914153017)
          ·
            refine ⟨3553042836485680435614763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737390448647573914153017 3553042836485680435614763)
            ·
              refine ⟨5329564254728520653422145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553042836485680435614763 5329564254728520653422145)
              ·
                refine ⟨3997173191046390490066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5329564254728520653422145 3997173191046390490066609)
                ·
                  refine ⟨2997879893284792867549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997173191046390490066609 2997879893284792867549957)
                  ·
                    refine ⟨562102479990898662665617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997879893284792867549957 562102479990898662665617)
                    ·
                      refine ⟨421576859993173996999213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562102479990898662665617 421576859993173996999213)
                      ·
                        rfl

theorem cell23_821018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_821018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821018 prefixEnd_821018 := by exact prefixLift 821018
  have htrace : WordTrace (prefixWord ++ tailWord_821018) baseStart_821018 baseEnd_821018 := by
    simpa [prefixWord, tailWord_821018, baseEnd_821018] using wordTrace_append hprefix tailTrace_821018
  have hstable : (prefixWord ++ tailWord_821018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821018).length < 2 ^ (prefixWord ++ tailWord_821018).sum := by decide
  have hdescent : baseEnd_821018 < baseStart_821018 := by decide
  rcases family_descends (prefixWord ++ tailWord_821018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821028 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_821028 : Nat := 118140960795 + 821028 * 2 ^ 59
def prefixEnd_821028 : Nat := 4983230072969 + 3 ^ 40 * 821028 * 2
def baseEnd_821028 : Nat := 140527331599906319291389

theorem tailTrace_821028 : CollatzResearch.WordTrace tailWord_821028 prefixEnd_821028 140527331599906319291389 := by
  unfold tailWord_821028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14972675634781625631995869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19963567513042167509327825 14972675634781625631995869)
  ·
    refine ⟨5614753363043109611998451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14972675634781625631995869 5614753363043109611998451)
    ·
      refine ⟨8422130044564664417997677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614753363043109611998451 8422130044564664417997677)
      ·
        refine ⟨3158298766711749156749129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8422130044564664417997677 3158298766711749156749129)
        ·
          refine ⟨2368724075033811867561847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3158298766711749156749129 2368724075033811867561847)
          ·
            refine ⟨3553086112550717801342771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368724075033811867561847 3553086112550717801342771)
            ·
              refine ⟨5329629168826076702014157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553086112550717801342771 5329629168826076702014157)
              ·
                refine ⟨1998610938309778763255309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5329629168826076702014157 1998610938309778763255309)
                ·
                  refine ⟨749479101866167036220741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1998610938309778763255309 749479101866167036220741)
                  ·
                    refine ⟨140527331599906319291389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749479101866167036220741 140527331599906319291389)
                    ·
                      rfl

theorem cell23_821028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_821028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821028 prefixEnd_821028 := by exact prefixLift 821028
  have htrace : WordTrace (prefixWord ++ tailWord_821028) baseStart_821028 baseEnd_821028 := by
    simpa [prefixWord, tailWord_821028, baseEnd_821028] using wordTrace_append hprefix tailTrace_821028
  have hstable : (prefixWord ++ tailWord_821028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821028).length < 2 ^ (prefixWord ++ tailWord_821028).sum := by decide
  have hdescent : baseEnd_821028 < baseStart_821028 := by decide
  rcases family_descends (prefixWord ++ tailWord_821028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821092 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 6]
def baseStart_821092 : Nat := 118140960795 + 821092 * 2 ^ 59
def prefixEnd_821092 : Nat := 4983230072969 + 3 ^ 40 * 821092 * 2
def baseEnd_821092 : Nat := 46846095284622967497097

theorem tailTrace_821092 : CollatzResearch.WordTrace tailWord_821092 prefixEnd_821092 46846095284622967497097 := by
  unfold tailWord_821092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14973842770665695097160765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19965123694220926796214353 14973842770665695097160765)
  ·
    refine ⟨5615191038999635661435287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14973842770665695097160765 5615191038999635661435287)
    ·
      refine ⟨8422786558499453492152931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615191038999635661435287 8422786558499453492152931)
      ·
        refine ⟨12634179837749180238229397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422786558499453492152931 12634179837749180238229397)
        ·
          refine ⟨592227179894492823667003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12634179837749180238229397 592227179894492823667003)
          ·
            refine ⟨888340769841739235500505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592227179894492823667003 888340769841739235500505)
            ·
              refine ⟨666255577381304426625379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888340769841739235500505 666255577381304426625379)
              ·
                refine ⟨999383366071956639938069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666255577381304426625379 999383366071956639938069)
                ·
                  refine ⟨46846095284622967497097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 999383366071956639938069 46846095284622967497097)
                  ·
                    rfl

theorem cell23_821092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_821092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821092 prefixEnd_821092 := by exact prefixLift 821092
  have htrace : WordTrace (prefixWord ++ tailWord_821092) baseStart_821092 baseEnd_821092 := by
    simpa [prefixWord, tailWord_821092, baseEnd_821092] using wordTrace_append hprefix tailTrace_821092
  have hstable : (prefixWord ++ tailWord_821092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821092).length < 2 ^ (prefixWord ++ tailWord_821092).sum := by decide
  have hdescent : baseEnd_821092 < baseStart_821092 := by decide
  rcases family_descends (prefixWord ++ tailWord_821092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821125 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_821125 : Nat := 118140960795 + 821125 * 2 ^ 59
def prefixEnd_821125 : Nat := 4983230072969 + 3 ^ 40 * 821125 * 2
def baseEnd_821125 : Nat := 421631802423205078361221

theorem tailTrace_821125 : CollatzResearch.WordTrace tailWord_821125 prefixEnd_821125 421631802423205078361221 := by
  unfold tailWord_821125
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948889150211836830272829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19965926100141224553515219 29948889150211836830272829)
  ·
    refine ⟨11230833431329438811352311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29948889150211836830272829 11230833431329438811352311)
    ·
      refine ⟨16846250146994158217028467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230833431329438811352311 16846250146994158217028467)
      ·
        refine ⟨25269375220491237325542701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16846250146994158217028467 25269375220491237325542701)
        ·
          refine ⟨9476015707684213997078513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25269375220491237325542701 9476015707684213997078513)
          ·
            refine ⟨7107011780763160497808885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476015707684213997078513 7107011780763160497808885)
            ·
              refine ⟨666282354446546296669583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7107011780763160497808885 666282354446546296669583)
              ·
                refine ⟨999423531669819445004375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666282354446546296669583 999423531669819445004375)
                ·
                  refine ⟨1499135297504729167506563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999423531669819445004375 1499135297504729167506563)
                  ·
                    refine ⟨2248702946257093751259845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1499135297504729167506563 2248702946257093751259845)
                    ·
                      refine ⟨421631802423205078361221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2248702946257093751259845 421631802423205078361221)
                      ·
                        rfl

theorem cell23_821125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_821125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821125 prefixEnd_821125 := by exact prefixLift 821125
  have htrace : WordTrace (prefixWord ++ tailWord_821125) baseStart_821125 baseEnd_821125 := by
    simpa [prefixWord, tailWord_821125, baseEnd_821125] using wordTrace_append hprefix tailTrace_821125
  have hstable : (prefixWord ++ tailWord_821125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821125).length < 2 ^ (prefixWord ++ tailWord_821125).sum := by decide
  have hdescent : baseEnd_821125 < baseStart_821125 := by decide
  rcases family_descends (prefixWord ++ tailWord_821125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821148 : List Nat := [2, 2, 3, 3, 1, 1, 3, 8]
def baseStart_821148 : Nat := 118140960795 + 821148 * 2 ^ 59
def prefixEnd_821148 : Nat := 4983230072969 + 3 ^ 40 * 821148 * 2
def baseEnd_821148 : Nat := 15616430091787351421245

theorem tailTrace_821148 : CollatzResearch.WordTrace tailWord_821148 prefixEnd_821148 15616430091787351421245 := by
  unfold tailWord_821148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14974864014564255879180049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19966485352752341172240065 14974864014564255879180049)
  ·
    refine ⟨11231148010923191909385037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14974864014564255879180049 11231148010923191909385037)
    ·
      refine ⟨4211680504096196966019389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11231148010923191909385037 4211680504096196966019389)
      ·
        refine ⟨1579380189036073862257271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4211680504096196966019389 1579380189036073862257271)
        ·
          refine ⟨2369070283554110793385907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579380189036073862257271 2369070283554110793385907)
          ·
            refine ⟨3553605425331166190078861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369070283554110793385907 3553605425331166190078861)
            ·
              refine ⟨1332602034499187321279573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553605425331166190078861 1332602034499187321279573)
              ·
                refine ⟨15616430091787351421245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1332602034499187321279573 15616430091787351421245)
                ·
                  rfl

theorem cell23_821148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 8].length) (baseStart_821148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821148 prefixEnd_821148 := by exact prefixLift 821148
  have htrace : WordTrace (prefixWord ++ tailWord_821148) baseStart_821148 baseEnd_821148 := by
    simpa [prefixWord, tailWord_821148, baseEnd_821148] using wordTrace_append hprefix tailTrace_821148
  have hstable : (prefixWord ++ tailWord_821148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821148).length < 2 ^ (prefixWord ++ tailWord_821148).sum := by decide
  have hdescent : baseEnd_821148 < baseStart_821148 := by decide
  rcases family_descends (prefixWord ++ tailWord_821148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821171 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_821171 : Nat := 118140960795 + 821171 * 2 ^ 59
def prefixEnd_821171 : Nat := 4983230072969 + 3 ^ 40 * 821171 * 2
def baseEnd_821171 : Nat := 421655422533311898386009

theorem tailTrace_821171 : CollatzResearch.WordTrace tailWord_821171 prefixEnd_821171 421655422533311898386009 := by
  unfold tailWord_821171
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950566908045186686447367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967044605363457790964911 29950566908045186686447367)
  ·
    refine ⟨44925850362067780029671051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29950566908045186686447367 44925850362067780029671051)
    ·
      refine ⟨67388775543101670044506577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44925850362067780029671051 67388775543101670044506577)
      ·
        refine ⟨50541581657326252533379933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67388775543101670044506577 50541581657326252533379933)
        ·
          refine ⟨18953093121497344700017475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50541581657326252533379933 18953093121497344700017475)
          ·
            refine ⟨28429639682246017050026213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953093121497344700017475 28429639682246017050026213)
            ·
              refine ⟨5330557440421128196879915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28429639682246017050026213 5330557440421128196879915)
              ·
                refine ⟨7995836160631692295319873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330557440421128196879915 7995836160631692295319873)
                ·
                  refine ⟨5996877120473769221489905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995836160631692295319873 5996877120473769221489905)
                  ·
                    refine ⟨4497657840355326916117429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5996877120473769221489905 4497657840355326916117429)
                    ·
                      refine ⟨421655422533311898386009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4497657840355326916117429 421655422533311898386009)
                      ·
                        rfl

theorem cell23_821171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_821171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821171 prefixEnd_821171 := by exact prefixLift 821171
  have htrace : WordTrace (prefixWord ++ tailWord_821171) baseStart_821171 baseEnd_821171 := by
    simpa [prefixWord, tailWord_821171, baseEnd_821171] using wordTrace_append hprefix tailTrace_821171
  have hstable : (prefixWord ++ tailWord_821171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821171).length < 2 ^ (prefixWord ++ tailWord_821171).sum := by decide
  have hdescent : baseEnd_821171 < baseStart_821171 := by decide
  rcases family_descends (prefixWord ++ tailWord_821171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821192 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_821192 : Nat := 118140960795 + 821192 * 2 ^ 59
def prefixEnd_821192 : Nat := 4983230072969 + 3 ^ 40 * 821192 * 2
def baseEnd_821192 : Nat := 421666205627056316223413

theorem tailTrace_821192 : CollatzResearch.WordTrace tailWord_821192 prefixEnd_821192 421666205627056316223413 := by
  unfold tailWord_821192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14975666420484553636480915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19967555227312738181974553 14975666420484553636480915)
  ·
    refine ⟨22463499630726830454721373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14975666420484553636480915 22463499630726830454721373)
    ·
      refine ⟨8423812361522561420520515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22463499630726830454721373 8423812361522561420520515)
      ·
        refine ⟨12635718542283842130780773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423812361522561420520515 12635718542283842130780773)
        ·
          refine ⟨2369197226678220399521395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12635718542283842130780773 2369197226678220399521395)
          ·
            refine ⟨3553795840017330599282093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369197226678220399521395 3553795840017330599282093)
            ·
              refine ⟨1332673440006498974730785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553795840017330599282093 1332673440006498974730785)
              ·
                refine ⟨999505080004874231048089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332673440006498974730785 999505080004874231048089)
                ·
                  refine ⟨749628810003655673286067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999505080004874231048089 749628810003655673286067)
                  ·
                    refine ⟨1124443215005483509929101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749628810003655673286067 1124443215005483509929101)
                    ·
                      refine ⟨421666205627056316223413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124443215005483509929101 421666205627056316223413)
                      ·
                        rfl

theorem cell23_821192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_821192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821192 prefixEnd_821192 := by exact prefixLift 821192
  have htrace : WordTrace (prefixWord ++ tailWord_821192) baseStart_821192 baseEnd_821192 := by
    simpa [prefixWord, tailWord_821192, baseEnd_821192] using wordTrace_append hprefix tailTrace_821192
  have hstable : (prefixWord ++ tailWord_821192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821192).length < 2 ^ (prefixWord ++ tailWord_821192).sum := by decide
  have hdescent : baseEnd_821192 < baseStart_821192 := by decide
  rcases family_descends (prefixWord ++ tailWord_821192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821201 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_821201 : Nat := 118140960795 + 821201 * 2 ^ 59
def prefixEnd_821201 : Nat := 4983230072969 + 3 ^ 40 * 821201 * 2
def baseEnd_821201 : Nat := 421670826952946781010871

theorem tailTrace_821201 : CollatzResearch.WordTrace tailWord_821201 prefixEnd_821201 421670826952946781010871 := by
  unfold tailWord_821201
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951661097936501810039457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967774065291001206692971 29951661097936501810039457)
  ·
    refine ⟨22463745823452376357529593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29951661097936501810039457 22463745823452376357529593)
    ·
      refine ⟨16847809367589282268147195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22463745823452376357529593 16847809367589282268147195)
      ·
        refine ⟨25271714051383923402220793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16847809367589282268147195 25271714051383923402220793)
        ·
          refine ⟨18953785538537942551665595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25271714051383923402220793 18953785538537942551665595)
          ·
            refine ⟨28430678307806913827498393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953785538537942551665595 28430678307806913827498393)
            ·
              refine ⟨21323008730855185370623795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28430678307806913827498393 21323008730855185370623795)
              ·
                refine ⟨31984513096282778055935693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21323008730855185370623795 31984513096282778055935693)
                ·
                  refine ⟨11994192411106041770975885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31984513096282778055935693 11994192411106041770975885)
                  ·
                    refine ⟨4497822154164765664115957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11994192411106041770975885 4497822154164765664115957)
                    ·
                      refine ⟨421670826952946781010871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4497822154164765664115957 421670826952946781010871)
                      ·
                        rfl

theorem cell23_821201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_821201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821201 prefixEnd_821201 := by exact prefixLift 821201
  have htrace : WordTrace (prefixWord ++ tailWord_821201) baseStart_821201 baseEnd_821201 := by
    simpa [prefixWord, tailWord_821201, baseEnd_821201] using wordTrace_append hprefix tailTrace_821201
  have hstable : (prefixWord ++ tailWord_821201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821201).length < 2 ^ (prefixWord ++ tailWord_821201).sum := by decide
  have hdescent : baseEnd_821201 < baseStart_821201 := by decide
  rcases family_descends (prefixWord ++ tailWord_821201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821209 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 2, 1, 3]
def baseStart_821209 : Nat := 118140960795 + 821209 * 2 ^ 59
def prefixEnd_821209 : Nat := 4983230072969 + 3 ^ 40 * 821209 * 2
def baseEnd_821209 : Nat := 421674934798182749710835

theorem tailTrace_821209 : CollatzResearch.WordTrace tailWord_821209 prefixEnd_821209 421674934798182749710835 := by
  unfold tailWord_821209
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951952881907519176330681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967968587938346117553787 29951952881907519176330681)
  ·
    refine ⟨22463964661430639382248011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29951952881907519176330681 22463964661430639382248011)
    ·
      refine ⟨33695946992145959073372017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22463964661430639382248011 33695946992145959073372017)
      ·
        refine ⟨25271960244109469305029013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33695946992145959073372017 25271960244109469305029013)
        ·
          refine ⟨1184623136442631373673235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25271960244109469305029013 1184623136442631373673235)
          ·
            refine ⟨1776934704663947060509853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184623136442631373673235 1776934704663947060509853)
            ·
              refine ⟨666350514248980147691195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776934704663947060509853 666350514248980147691195)
              ·
                refine ⟨999525771373470221536793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666350514248980147691195 999525771373470221536793)
                ·
                  refine ⟨749644328530102666152595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999525771373470221536793 749644328530102666152595)
                  ·
                    refine ⟨1124466492795153999228893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749644328530102666152595 1124466492795153999228893)
                    ·
                      refine ⟨421674934798182749710835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124466492795153999228893 421674934798182749710835)
                      ·
                        rfl

theorem cell23_821209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_821209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821209 prefixEnd_821209 := by exact prefixLift 821209
  have htrace : WordTrace (prefixWord ++ tailWord_821209) baseStart_821209 baseEnd_821209 := by
    simpa [prefixWord, tailWord_821209, baseEnd_821209] using wordTrace_append hprefix tailTrace_821209
  have hstable : (prefixWord ++ tailWord_821209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821209).length < 2 ^ (prefixWord ++ tailWord_821209).sum := by decide
  have hdescent : baseEnd_821209 < baseStart_821209 := by decide
  rcases family_descends (prefixWord ++ tailWord_821209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821248 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_821248 : Nat := 118140960795 + 821248 * 2 ^ 59
def prefixEnd_821248 : Nat := 4983230072969 + 3 ^ 40 * 821248 * 2
def baseEnd_821248 : Nat := 421694960543708097123155

theorem tailTrace_821248 : CollatzResearch.WordTrace tailWord_821248 prefixEnd_821248 421694960543708097123155 := by
  unfold tailWord_821248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976687664383114418500199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19968916885844152558000265 14976687664383114418500199)
  ·
    refine ⟨22465031496574671627750299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14976687664383114418500199 22465031496574671627750299)
    ·
      refine ⟨33697547244862007441625449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22465031496574671627750299 33697547244862007441625449)
      ·
        refine ⟨25273160433646505581219087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33697547244862007441625449 25273160433646505581219087)
        ·
          refine ⟨37909740650469758371828631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273160433646505581219087 37909740650469758371828631)
          ·
            refine ⟨56864610975704637557742947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37909740650469758371828631 56864610975704637557742947)
            ·
              refine ⟨85296916463556956336614421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56864610975704637557742947 85296916463556956336614421)
              ·
                refine ⟨3998292959229232328278801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85296916463556956336614421 3998292959229232328278801)
                ·
                  refine ⟨2998719719421924246209101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998292959229232328278801 2998719719421924246209101)
                  ·
                    refine ⟨1124519894783221592328413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998719719421924246209101 1124519894783221592328413)
                    ·
                      refine ⟨421694960543708097123155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124519894783221592328413 421694960543708097123155)
                      ·
                        rfl

theorem cell23_821248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_821248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821248 prefixEnd_821248 := by exact prefixLift 821248
  have htrace : WordTrace (prefixWord ++ tailWord_821248) baseStart_821248 baseEnd_821248 := by
    simpa [prefixWord, tailWord_821248, baseEnd_821248] using wordTrace_append hprefix tailTrace_821248
  have hstable : (prefixWord ++ tailWord_821248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821248).length < 2 ^ (prefixWord ++ tailWord_821248).sum := by decide
  have hdescent : baseEnd_821248 < baseStart_821248 := by decide
  rcases family_descends (prefixWord ++ tailWord_821248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821255 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 7]
def baseStart_821255 : Nat := 118140960795 + 821255 * 2 ^ 59
def prefixEnd_821255 : Nat := 4983230072969 + 3 ^ 40 * 821255 * 2
def baseEnd_821255 : Nat := 46855394989809952192847

theorem tailTrace_821255 : CollatzResearch.WordTrace tailWord_821255 prefixEnd_821255 46855394989809952192847 := by
  unfold tailWord_821255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953630639740869032505219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19969087093160579355003479 29953630639740869032505219)
  ·
    refine ⟨44930445959611303548757829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29953630639740869032505219 44930445959611303548757829)
    ·
      refine ⟨8424458617427119415392093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44930445959611303548757829 8424458617427119415392093)
      ·
        refine ⟨3159171981535169780772035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8424458617427119415392093 3159171981535169780772035)
        ·
          refine ⟨4738757972302754671158053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159171981535169780772035 4738757972302754671158053)
          ·
            refine ⟨888517119806766500842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4738757972302754671158053 888517119806766500842135)
            ·
              refine ⟨1332775679710149751263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888517119806766500842135 1332775679710149751263203)
              ·
                refine ⟨1999163519565224626894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332775679710149751263203 1999163519565224626894805)
                ·
                  refine ⟨46855394989809952192847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1999163519565224626894805 46855394989809952192847)
                  ·
                    rfl

theorem cell23_821255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 7].length) (baseStart_821255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821255 prefixEnd_821255 := by exact prefixLift 821255
  have htrace : WordTrace (prefixWord ++ tailWord_821255) baseStart_821255 baseEnd_821255 := by
    simpa [prefixWord, tailWord_821255, baseEnd_821255] using wordTrace_append hprefix tailTrace_821255
  have hstable : (prefixWord ++ tailWord_821255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821255).length < 2 ^ (prefixWord ++ tailWord_821255).sum := by decide
  have hdescent : baseEnd_821255 < baseStart_821255 := by decide
  rcases family_descends (prefixWord ++ tailWord_821255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821285 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_821285 : Nat := 118140960795 + 821285 * 2 ^ 59
def prefixEnd_821285 : Nat := 4983230072969 + 3 ^ 40 * 821285 * 2
def baseEnd_821285 : Nat := 140571319775974817453495

theorem tailTrace_821285 : CollatzResearch.WordTrace tailWord_821285 prefixEnd_821285 140571319775974817453495 := by
  unfold tailWord_821285
  simp only [CollatzResearch.WordTrace]
  refine ⟨29954724829632184156097309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19969816553088122770731539 29954724829632184156097309)
  ·
    refine ⟨11233021811112069058536491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29954724829632184156097309 11233021811112069058536491)
    ·
      refine ⟨16849532716668103587804737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11233021811112069058536491 16849532716668103587804737)
      ·
        refine ⟨12637149537501077690853553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16849532716668103587804737 12637149537501077690853553)
        ·
          refine ⟨9477862153125808268140165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12637149537501077690853553 9477862153125808268140165)
          ·
            refine ⟨1777099153711089050276281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9477862153125808268140165 1777099153711089050276281)
            ·
              refine ⟨1332824365283316787707211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777099153711089050276281 1332824365283316787707211)
              ·
                refine ⟨1999236547924975181560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332824365283316787707211 1999236547924975181560817)
                ·
                  refine ⟨1499427410943731386170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1999236547924975181560817 1499427410943731386170613)
                  ·
                    refine ⟨140571319775974817453495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1499427410943731386170613 140571319775974817453495)
                    ·
                      rfl

theorem cell23_821285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_821285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821285 prefixEnd_821285 := by exact prefixLift 821285
  have htrace : WordTrace (prefixWord ++ tailWord_821285) baseStart_821285 baseEnd_821285 := by
    simpa [prefixWord, tailWord_821285, baseEnd_821285] using wordTrace_append hprefix tailTrace_821285
  have hstable : (prefixWord ++ tailWord_821285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821285).length < 2 ^ (prefixWord ++ tailWord_821285).sum := by decide
  have hdescent : baseEnd_821285 < baseStart_821285 := by decide
  rcases family_descends (prefixWord ++ tailWord_821285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821308 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_821308 : Nat := 118140960795 + 821308 * 2 ^ 59
def prefixEnd_821308 : Nat := 4983230072969 + 3 ^ 40 * 821308 * 2
def baseEnd_821308 : Nat := 421725769382977862372879

theorem tailTrace_821308 : CollatzResearch.WordTrace tailWord_821308 prefixEnd_821308 421725769382977862372879 := by
  unfold tailWord_821308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977781854274429542092289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19970375805699239389456385 14977781854274429542092289)
  ·
    refine ⟨11233336390705822156569217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14977781854274429542092289 11233336390705822156569217)
    ·
      refine ⟨8425002293029366617426913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11233336390705822156569217 8425002293029366617426913)
      ·
        refine ⟨6318751719772024963070185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8425002293029366617426913 6318751719772024963070185)
        ·
          refine ⟨4739063789829018722302639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318751719772024963070185 4739063789829018722302639)
          ·
            refine ⟨7108595684743528083453959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739063789829018722302639 7108595684743528083453959)
            ·
              refine ⟨10662893527115292125180939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108595684743528083453959 10662893527115292125180939)
              ·
                refine ⟨15994340290672938187771409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662893527115292125180939 15994340290672938187771409)
                ·
                  refine ⟨11995755218004703640828557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15994340290672938187771409 11995755218004703640828557)
                  ·
                    refine ⟨4498408206751763865310709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11995755218004703640828557 4498408206751763865310709)
                    ·
                      refine ⟨421725769382977862372879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4498408206751763865310709 421725769382977862372879)
                      ·
                        rfl

theorem cell23_821308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_821308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821308 prefixEnd_821308 := by exact prefixLift 821308
  have htrace : WordTrace (prefixWord ++ tailWord_821308) baseStart_821308 baseEnd_821308 := by
    simpa [prefixWord, tailWord_821308, baseEnd_821308] using wordTrace_append hprefix tailTrace_821308
  have hstable : (prefixWord ++ tailWord_821308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821308).length < 2 ^ (prefixWord ++ tailWord_821308).sum := by decide
  have hdescent : baseEnd_821308 < baseStart_821308 := by decide
  rcases family_descends (prefixWord ++ tailWord_821308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821349 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_821349 : Nat := 118140960795 + 821349 * 2 ^ 59
def prefixEnd_821349 : Nat := 4983230072969 + 3 ^ 40 * 821349 * 2
def baseEnd_821349 : Nat := 140582274029937400653397

theorem tailTrace_821349 : CollatzResearch.WordTrace tailWord_821349 prefixEnd_821349 140582274029937400653397 := by
  unfold tailWord_821349
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957059101400323086427101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19971372734266882057618067 29957059101400323086427101)
  ·
    refine ⟨11233897163025121157410163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29957059101400323086427101 11233897163025121157410163)
    ·
      refine ⟨16850845744537681736115245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11233897163025121157410163 16850845744537681736115245)
      ·
        refine ⟨6319067154201630651043217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16850845744537681736115245 6319067154201630651043217)
        ·
          refine ⟨4739300365651222988282413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319067154201630651043217 4739300365651222988282413)
          ·
            refine ⟨1777237637119208620605905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4739300365651222988282413 1777237637119208620605905)
            ·
              refine ⟨1332928227839406465454429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777237637119208620605905 1332928227839406465454429)
              ·
                refine ⟨499848085439777424545411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1332928227839406465454429 499848085439777424545411)
                ·
                  refine ⟨749772128159666136818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499848085439777424545411 749772128159666136818117)
                  ·
                    refine ⟨140582274029937400653397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749772128159666136818117 140582274029937400653397)
                    ·
                      rfl

theorem cell23_821349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_821349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821349 prefixEnd_821349 := by exact prefixLift 821349
  have htrace : WordTrace (prefixWord ++ tailWord_821349) baseStart_821349 baseEnd_821349 := by
    simpa [prefixWord, tailWord_821349, baseEnd_821349] using wordTrace_append hprefix tailTrace_821349
  have hstable : (prefixWord ++ tailWord_821349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821349).length < 2 ^ (prefixWord ++ tailWord_821349).sum := by decide
  have hdescent : baseEnd_821349 < baseStart_821349 := by decide
  rcases family_descends (prefixWord ++ tailWord_821349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821362 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_821362 : Nat := 118140960795 + 821362 * 2 ^ 59
def prefixEnd_821362 : Nat := 4983230072969 + 3 ^ 40 * 821362 * 2
def baseEnd_821362 : Nat := 46861499704257850121959

theorem tailTrace_821362 : CollatzResearch.WordTrace tailWord_821362 prefixEnd_821362 46861499704257850121959 := by
  unfold tailWord_821362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7489383312588306576662585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19971688833568817537766893 7489383312588306576662585)
  ·
    refine ⟨5617037484441229932496939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7489383312588306576662585 5617037484441229932496939)
    ·
      refine ⟨8425556226661844898745409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617037484441229932496939 8425556226661844898745409)
      ·
        refine ⟨6319167169996383674059057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8425556226661844898745409 6319167169996383674059057)
        ·
          refine ⟨4739375377497287755544293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319167169996383674059057 4739375377497287755544293)
          ·
            refine ⟨888632883280741454164555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4739375377497287755544293 888632883280741454164555)
            ·
              refine ⟨1332949324921112181246833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888632883280741454164555 1332949324921112181246833)
              ·
                refine ⟨999711993690834135935125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332949324921112181246833 999711993690834135935125)
                ·
                  refine ⟨46861499704257850121959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 999711993690834135935125 46861499704257850121959)
                  ·
                    rfl

theorem cell23_821362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_821362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821362 prefixEnd_821362 := by exact prefixLift 821362
  have htrace : WordTrace (prefixWord ++ tailWord_821362) baseStart_821362 baseEnd_821362 := by
    simpa [prefixWord, tailWord_821362, baseEnd_821362] using wordTrace_append hprefix tailTrace_821362
  have hstable : (prefixWord ++ tailWord_821362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821362).length < 2 ^ (prefixWord ++ tailWord_821362).sum := by decide
  have hdescent : baseEnd_821362 < baseStart_821362 := by decide
  rcases family_descends (prefixWord ++ tailWord_821362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821372 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_821372 : Nat := 118140960795 + 821372 * 2 ^ 59
def prefixEnd_821372 : Nat := 4983230072969 + 3 ^ 40 * 821372 * 2
def baseEnd_821372 : Nat := 421758632144865611972585

theorem tailTrace_821372 : CollatzResearch.WordTrace tailWord_821372 prefixEnd_821372 421758632144865611972585 := by
  unfold tailWord_821372
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978948990158499007257185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19971931986877998676342913 14978948990158499007257185)
  ·
    refine ⟨11234211742618874255442889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14978948990158499007257185 11234211742618874255442889)
    ·
      refine ⟨8425658806964155691582167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11234211742618874255442889 8425658806964155691582167)
      ·
        refine ⟨12638488210446233537373251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8425658806964155691582167 12638488210446233537373251)
        ·
          refine ⟨18957732315669350306059877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638488210446233537373251 18957732315669350306059877)
          ·
            refine ⟨3554574809188003182386227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18957732315669350306059877 3554574809188003182386227)
            ·
              refine ⟨5331862213782004773579341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554574809188003182386227 5331862213782004773579341)
              ·
                refine ⟨1999448330168251790092253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5331862213782004773579341 1999448330168251790092253)
                ·
                  refine ⟨749793123813094421284595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1999448330168251790092253 749793123813094421284595)
                  ·
                    refine ⟨1124689685719641631926893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749793123813094421284595 1124689685719641631926893)
                    ·
                      refine ⟨421758632144865611972585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124689685719641631926893 421758632144865611972585)
                      ·
                        rfl

theorem cell23_821372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_821372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821372 prefixEnd_821372 := by exact prefixLift 821372
  have htrace : WordTrace (prefixWord ++ tailWord_821372) baseStart_821372 baseEnd_821372 := by
    simpa [prefixWord, tailWord_821372, baseEnd_821372] using wordTrace_append hprefix tailTrace_821372
  have hstable : (prefixWord ++ tailWord_821372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821372).length < 2 ^ (prefixWord ++ tailWord_821372).sum := by decide
  have hdescent : baseEnd_821372 < baseStart_821372 := by decide
  rcases family_descends (prefixWord ++ tailWord_821372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821395 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 8, 2]
def baseStart_821395 : Nat := 118140960795 + 821395 * 2 ^ 59
def prefixEnd_821395 : Nat := 4983230072969 + 3 ^ 40 * 821395 * 2
def baseEnd_821395 : Nat := 421770442199919021984979

theorem tailTrace_821395 : CollatzResearch.WordTrace tailWord_821395 prefixEnd_821395 421770442199919021984979 := by
  unfold tailWord_821395
  simp only [CollatzResearch.WordTrace]
  refine ⟨29958736859233672942601639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19972491239489115295067759 29958736859233672942601639)
  ·
    refine ⟨44938105288850509413902459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29958736859233672942601639 44938105288850509413902459)
    ·
      refine ⟨67407157933275764120853689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44938105288850509413902459 67407157933275764120853689)
      ·
        refine ⟨50555368449956823090640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67407157933275764120853689 50555368449956823090640267)
        ·
          refine ⟨75833052674935234635960401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50555368449956823090640267 75833052674935234635960401)
          ·
            refine ⟨56874789506201425976970301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75833052674935234635960401 56874789506201425976970301)
            ·
              refine ⟨21328046064825534741363863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56874789506201425976970301 21328046064825534741363863)
              ·
                refine ⟨31992069097238302112045795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21328046064825534741363863 31992069097238302112045795)
                ·
                  refine ⟨47988103645857453168068693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31992069097238302112045795 47988103645857453168068693)
                  ·
                    refine ⟨562360589599892029313305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47988103645857453168068693 562360589599892029313305)
                    ·
                      refine ⟨421770442199919021984979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562360589599892029313305 421770442199919021984979)
                      ·
                        rfl

theorem cell23_821395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8, 2].length) (baseStart_821395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821395 prefixEnd_821395 := by exact prefixLift 821395
  have htrace : WordTrace (prefixWord ++ tailWord_821395) baseStart_821395 baseEnd_821395 := by
    simpa [prefixWord, tailWord_821395, baseEnd_821395] using wordTrace_append hprefix tailTrace_821395
  have hstable : (prefixWord ++ tailWord_821395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821395).length < 2 ^ (prefixWord ++ tailWord_821395).sum := by decide
  have hdescent : baseEnd_821395 < baseStart_821395 := by decide
  rcases family_descends (prefixWord ++ tailWord_821395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821474 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_821474 : Nat := 118140960795 + 821474 * 2 ^ 59
def prefixEnd_821474 : Nat := 4983230072969 + 3 ^ 40 * 821474 * 2
def baseEnd_821474 : Nat := 421811007171624212897117

theorem tailTrace_821474 : CollatzResearch.WordTrace tailWord_821474 prefixEnd_821474 421811007171624212897117 := by
  unfold tailWord_821474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490404556486867358681869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19974412150631646289818317 7490404556486867358681869)
  ·
    refine ⟨2808901708682575259505701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7490404556486867358681869 2808901708682575259505701)
    ·
      refine ⟨526669070377982861157319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2808901708682575259505701 526669070377982861157319)
      ·
        refine ⟨790003605566974291735979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526669070377982861157319 790003605566974291735979)
        ·
          refine ⟨1185005408350461437603969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790003605566974291735979 1185005408350461437603969)
          ·
            refine ⟨888754056262846078202977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185005408350461437603969 888754056262846078202977)
            ·
              refine ⟨666565542197134558652233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888754056262846078202977 666565542197134558652233)
              ·
                refine ⟨499924156647850918989175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666565542197134558652233 499924156647850918989175)
                ·
                  refine ⟨749886234971776378483763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499924156647850918989175 749886234971776378483763)
                  ·
                    refine ⟨1124829352457664567725645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749886234971776378483763 1124829352457664567725645)
                    ·
                      refine ⟨421811007171624212897117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1124829352457664567725645 421811007171624212897117)
                      ·
                        rfl

theorem cell23_821474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_821474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821474 prefixEnd_821474 := by exact prefixLift 821474
  have htrace : WordTrace (prefixWord ++ tailWord_821474) baseStart_821474 baseEnd_821474 := by
    simpa [prefixWord, tailWord_821474, baseEnd_821474] using wordTrace_append hprefix tailTrace_821474
  have hstable : (prefixWord ++ tailWord_821474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821474).length < 2 ^ (prefixWord ++ tailWord_821474).sum := by decide
  have hdescent : baseEnd_821474 < baseStart_821474 := by decide
  rcases family_descends (prefixWord ++ tailWord_821474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821480 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_821480 : Nat := 118140960795 + 821480 * 2 ^ 59
def prefixEnd_821480 : Nat := 4983230072969 + 3 ^ 40 * 821480 * 2
def baseEnd_821480 : Nat := 421814088055551189422089

theorem tailTrace_821480 : CollatzResearch.WordTrace tailWord_821480 prefixEnd_821480 421814088055551189422089 := by
  unfold tailWord_821480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980918531962866229722947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19974558042617154972963929 14980918531962866229722947)
  ·
    refine ⟨22471377797944299344584421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14980918531962866229722947 22471377797944299344584421)
    ·
      refine ⟨4213383337114556127109579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22471377797944299344584421 4213383337114556127109579)
      ·
        refine ⟨6320075005671834190664369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213383337114556127109579 6320075005671834190664369)
        ·
          refine ⟨4740056254253875642998277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6320075005671834190664369 4740056254253875642998277)
          ·
            refine ⟨888760547672601683062177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4740056254253875642998277 888760547672601683062177)
            ·
              refine ⟨666570410754451262296633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888760547672601683062177 666570410754451262296633)
              ·
                refine ⟨499927808065838446722475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666570410754451262296633 499927808065838446722475)
                ·
                  refine ⟨749891712098757670083713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499927808065838446722475 749891712098757670083713)
                  ·
                    refine ⟨562418784074068252562785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 749891712098757670083713 562418784074068252562785)
                    ·
                      refine ⟨421814088055551189422089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562418784074068252562785 421814088055551189422089)
                      ·
                        rfl

theorem cell23_821480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_821480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821480 prefixEnd_821480 := by exact prefixLift 821480
  have htrace : WordTrace (prefixWord ++ tailWord_821480) baseStart_821480 baseEnd_821480 := by
    simpa [prefixWord, tailWord_821480, baseEnd_821480] using wordTrace_append hprefix tailTrace_821480
  have hstable : (prefixWord ++ tailWord_821480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821480).length < 2 ^ (prefixWord ++ tailWord_821480).sum := by decide
  have hdescent : baseEnd_821480 < baseStart_821480 := by decide
  rcases family_descends (prefixWord ++ tailWord_821480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821502 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_821502 : Nat := 118140960795 + 821502 * 2 ^ 59
def prefixEnd_821502 : Nat := 4983230072969 + 3 ^ 40 * 821502 * 2
def baseEnd_821502 : Nat := 421825384629950103346987

theorem tailTrace_821502 : CollatzResearch.WordTrace tailWord_821502 prefixEnd_821502 421825384629950103346987 := by
  unfold tailWord_821502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745329933730753777093345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19975092979897353477831173 3745329933730753777093345)
  ·
    refine ⟨2808997450298065332820009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3745329933730753777093345 2808997450298065332820009)
    ·
      refine ⟨2106748087723548999615007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808997450298065332820009 2106748087723548999615007)
      ·
        refine ⟨3160122131585323499422511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106748087723548999615007 3160122131585323499422511)
        ·
          refine ⟨4740183197377985249133767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160122131585323499422511 4740183197377985249133767)
          ·
            refine ⟨7110274796066977873700651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740183197377985249133767 7110274796066977873700651)
            ·
              refine ⟨10665412194100466810550977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110274796066977873700651 10665412194100466810550977)
              ·
                refine ⟨7999059145575350107913233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665412194100466810550977 7999059145575350107913233)
                ·
                  refine ⟨5999294359181512580934925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7999059145575350107913233 5999294359181512580934925)
                  ·
                    refine ⟨2249735384693067217850597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5999294359181512580934925 2249735384693067217850597)
                    ·
                      refine ⟨421825384629950103346987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2249735384693067217850597 421825384629950103346987)
                      ·
                        rfl

theorem cell23_821502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_821502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821502 prefixEnd_821502 := by exact prefixLift 821502
  have htrace : WordTrace (prefixWord ++ tailWord_821502) baseStart_821502 baseEnd_821502 := by
    simpa [prefixWord, tailWord_821502, baseEnd_821502] using wordTrace_append hprefix tailTrace_821502
  have hstable : (prefixWord ++ tailWord_821502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821502).length < 2 ^ (prefixWord ++ tailWord_821502).sum := by decide
  have hdescent : baseEnd_821502 < baseStart_821502 := by decide
  rcases family_descends (prefixWord ++ tailWord_821502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821506 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_821506 : Nat := 118140960795 + 821506 * 2 ^ 59
def prefixEnd_821506 : Nat := 4983230072969 + 3 ^ 40 * 821506 * 2
def baseEnd_821506 : Nat := 421827438552568087696969

theorem tailTrace_821506 : CollatzResearch.WordTrace tailWord_821506 prefixEnd_821506 421827438552568087696969 := by
  unfold tailWord_821506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490696340457884724973093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19975190241221025933261581 7490696340457884724973093)
  ·
    refine ⟨1404505563835853385932455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7490696340457884724973093 1404505563835853385932455)
    ·
      refine ⟨2106758345753780078898683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404505563835853385932455 2106758345753780078898683)
      ·
        refine ⟨3160137518630670118348025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106758345753780078898683 3160137518630670118348025)
        ·
          refine ⟨2370103138973002588761019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160137518630670118348025 2370103138973002588761019)
          ·
            refine ⟨3555154708459503883141529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370103138973002588761019 3555154708459503883141529)
            ·
              refine ⟨2666366031344627912356147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555154708459503883141529 2666366031344627912356147)
              ·
                refine ⟨3999549047016941868534221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666366031344627912356147 3999549047016941868534221)
                ·
                  refine ⟨1499830892631353200700333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3999549047016941868534221 1499830892631353200700333)
                  ·
                    refine ⟨562436584736757450262625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1499830892631353200700333 562436584736757450262625)
                    ·
                      refine ⟨421827438552568087696969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562436584736757450262625 421827438552568087696969)
                      ·
                        rfl

theorem cell23_821506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_821506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821506 prefixEnd_821506 := by exact prefixLift 821506
  have htrace : WordTrace (prefixWord ++ tailWord_821506) baseStart_821506 baseEnd_821506 := by
    simpa [prefixWord, tailWord_821506, baseEnd_821506] using wordTrace_append hprefix tailTrace_821506
  have hstable : (prefixWord ++ tailWord_821506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821506).length < 2 ^ (prefixWord ++ tailWord_821506).sum := by decide
  have hdescent : baseEnd_821506 < baseStart_821506 := by decide
  rcases family_descends (prefixWord ++ tailWord_821506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821515 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_821515 : Nat := 118140960795 + 821515 * 2 ^ 59
def prefixEnd_821515 : Nat := 4983230072969 + 3 ^ 40 * 821515 * 2
def baseEnd_821515 : Nat := 421832059878458552484427

theorem tailTrace_821515 : CollatzResearch.WordTrace tailWord_821515 prefixEnd_821515 421832059878458552484427 := by
  unfold tailWord_821515
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963113618798933436969999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19975409079199288957979999 29963113618798933436969999)
  ·
    refine ⟨44944670428198400155454999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29963113618798933436969999 44944670428198400155454999)
    ·
      refine ⟨67417005642297600233182499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44944670428198400155454999 67417005642297600233182499)
      ·
        refine ⟨101125508463446400349773749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67417005642297600233182499 101125508463446400349773749)
        ·
          refine ⟨9480516418448100032791289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101125508463446400349773749 9480516418448100032791289)
          ·
            refine ⟨7110387313836075024593467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9480516418448100032791289 7110387313836075024593467)
            ·
              refine ⟨10665580970754112536890201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110387313836075024593467 10665580970754112536890201)
              ·
                refine ⟨7999185728065584402667651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665580970754112536890201 7999185728065584402667651)
                ·
                  refine ⟨11998778592098376604001477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7999185728065584402667651 11998778592098376604001477)
                  ·
                    refine ⟨2249770986018445613250277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11998778592098376604001477 2249770986018445613250277)
                    ·
                      refine ⟨421832059878458552484427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2249770986018445613250277 421832059878458552484427)
                      ·
                        rfl

theorem cell23_821515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_821515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821515 prefixEnd_821515 := by exact prefixLift 821515
  have htrace : WordTrace (prefixWord ++ tailWord_821515) baseStart_821515 baseEnd_821515 := by
    simpa [prefixWord, tailWord_821515, baseEnd_821515] using wordTrace_append hprefix tailTrace_821515
  have hstable : (prefixWord ++ tailWord_821515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821515).length < 2 ^ (prefixWord ++ tailWord_821515).sum := by decide
  have hdescent : baseEnd_821515 < baseStart_821515 := by decide
  rcases family_descends (prefixWord ++ tailWord_821515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821536 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2]
def baseStart_821536 : Nat := 118140960795 + 821536 * 2 ^ 59
def prefixEnd_821536 : Nat := 4983230072969 + 3 ^ 40 * 821536 * 2
def baseEnd_821536 : Nat := 421842842972202970321831

theorem tailTrace_821536 : CollatzResearch.WordTrace tailWord_821536 prefixEnd_821536 421842842972202970321831 := by
  unfold tailWord_821536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981939775861427011742231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19975919701148569348989641 14981939775861427011742231)
  ·
    refine ⟨22472909663792140517613347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981939775861427011742231 22472909663792140517613347)
    ·
      refine ⟨33709364495688210776420021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472909663792140517613347 33709364495688210776420021)
      ·
        refine ⟨3160252921470769760289377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33709364495688210776420021 3160252921470769760289377)
        ·
          refine ⟨2370189691103077320217033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160252921470769760289377 2370189691103077320217033)
          ·
            refine ⟨1777642268327307990162775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370189691103077320217033 1777642268327307990162775)
            ·
              refine ⟨2666463402490961985244163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777642268327307990162775 2666463402490961985244163)
              ·
                refine ⟨3999695103736442977866245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666463402490961985244163 3999695103736442977866245)
                ·
                  refine ⟨749942831950583058349921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3999695103736442977866245 749942831950583058349921)
                  ·
                    refine ⟨562457123962937293762441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 749942831950583058349921 562457123962937293762441)
                    ·
                      refine ⟨421842842972202970321831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562457123962937293762441 421842842972202970321831)
                      ·
                        rfl

theorem cell23_821536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_821536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821536 prefixEnd_821536 := by exact prefixLift 821536
  have htrace : WordTrace (prefixWord ++ tailWord_821536) baseStart_821536 baseEnd_821536 := by
    simpa [prefixWord, tailWord_821536, baseEnd_821536] using wordTrace_append hprefix tailTrace_821536
  have hstable : (prefixWord ++ tailWord_821536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821536).length < 2 ^ (prefixWord ++ tailWord_821536).sum := by decide
  have hdescent : baseEnd_821536 < baseStart_821536 := by decide
  rcases family_descends (prefixWord ++ tailWord_821536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821553 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_821553 : Nat := 118140960795 + 821553 * 2 ^ 59
def prefixEnd_821553 : Nat := 4983230072969 + 3 ^ 40 * 821553 * 2
def baseEnd_821553 : Nat := 421851572143329403809253

theorem tailTrace_821553 : CollatzResearch.WordTrace tailWord_821553 prefixEnd_821553 421851572143329403809253 := by
  unfold tailWord_821553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964499592661265926853313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19976333061774177284568875 29964499592661265926853313)
  ·
    refine ⟨22473374694495949445139985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29964499592661265926853313 22473374694495949445139985)
    ·
      refine ⟨16855031020871962083854989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22473374694495949445139985 16855031020871962083854989)
      ·
        refine ⟨6320636632826985781445621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16855031020871962083854989 6320636632826985781445621)
        ·
          refine ⟨592559684327529917010527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6320636632826985781445621 592559684327529917010527)
          ·
            refine ⟨888839526491294875515791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592559684327529917010527 888839526491294875515791)
            ·
              refine ⟨1333259289736942313273687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888839526491294875515791 1333259289736942313273687)
              ·
                refine ⟨1999888934605413469910531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333259289736942313273687 1999888934605413469910531)
                ·
                  refine ⟨2999833401908120204865797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999888934605413469910531 2999833401908120204865797)
                  ·
                    refine ⟨562468762857772538412337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999833401908120204865797 562468762857772538412337)
                    ·
                      refine ⟨421851572143329403809253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562468762857772538412337 421851572143329403809253)
                      ·
                        rfl

theorem cell23_821553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_821553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821553 prefixEnd_821553 := by exact prefixLift 821553
  have htrace : WordTrace (prefixWord ++ tailWord_821553) baseStart_821553 baseEnd_821553 := by
    simpa [prefixWord, tailWord_821553, baseEnd_821553] using wordTrace_append hprefix tailTrace_821553
  have hstable : (prefixWord ++ tailWord_821553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821553).length < 2 ^ (prefixWord ++ tailWord_821553).sum := by decide
  have hdescent : baseEnd_821553 < baseStart_821553 := by decide
  rcases family_descends (prefixWord ++ tailWord_821553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821555 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 7]
def baseStart_821555 : Nat := 118140960795 + 821555 * 2 ^ 59
def prefixEnd_821555 : Nat := 4983230072969 + 3 ^ 40 * 821555 * 2
def baseEnd_821555 : Nat := 140617533034879465328081

theorem tailTrace_821555 : CollatzResearch.WordTrace tailWord_821555 prefixEnd_821555 140617533034879465328081 := by
  unfold tailWord_821555
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964572538654020268426119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19976381692436013512284079 29964572538654020268426119)
  ·
    refine ⟨44946858807981030402639179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29964572538654020268426119 44946858807981030402639179)
    ·
      refine ⟨67420288211971545603958769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44946858807981030402639179 67420288211971545603958769)
      ·
        refine ⟨50565216158978659202969077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67420288211971545603958769 50565216158978659202969077)
        ·
          refine ⟨4740489014904249300278351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50565216158978659202969077 4740489014904249300278351)
          ·
            refine ⟨7110733522356373950417527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740489014904249300278351 7110733522356373950417527)
            ·
              refine ⟨10666100283534560925626291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110733522356373950417527 10666100283534560925626291)
              ·
                refine ⟨15999150425301841388439437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10666100283534560925626291 15999150425301841388439437)
                ·
                  refine ⟨5999681409488190520664789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15999150425301841388439437 5999681409488190520664789)
                  ·
                    refine ⟨140617533034879465328081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5999681409488190520664789 140617533034879465328081)
                    ·
                      rfl

theorem cell23_821555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_821555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821555 prefixEnd_821555 := by exact prefixLift 821555
  have htrace : WordTrace (prefixWord ++ tailWord_821555) baseStart_821555 baseEnd_821555 := by
    simpa [prefixWord, tailWord_821555, baseEnd_821555] using wordTrace_append hprefix tailTrace_821555
  have hstable : (prefixWord ++ tailWord_821555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821555).length < 2 ^ (prefixWord ++ tailWord_821555).sum := by decide
  have hdescent : baseEnd_821555 < baseStart_821555 := by decide
  rcases family_descends (prefixWord ++ tailWord_821555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821589 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_821589 : Nat := 118140960795 + 821589 * 2 ^ 59
def prefixEnd_821589 : Nat := 4983230072969 + 3 ^ 40 * 821589 * 2
def baseEnd_821589 : Nat := 140623352482297087653029

theorem tailTrace_821589 : CollatzResearch.WordTrace tailWord_821589 prefixEnd_821589 140623352482297087653029 := by
  unfold tailWord_821589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29965812620530844075163821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19977208413687229383442547 29965812620530844075163821)
  ·
    refine ⟨11237179732699066528186433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29965812620530844075163821 11237179732699066528186433)
    ·
      refine ⟨8427884799524299896139825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11237179732699066528186433 8427884799524299896139825)
      ·
        refine ⟨6320913599643224922104869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8427884799524299896139825 6320913599643224922104869)
        ·
          refine ⟨1185171299933104672894663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6320913599643224922104869 1185171299933104672894663)
          ·
            refine ⟨1777756949899657009341995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185171299933104672894663 1777756949899657009341995)
            ·
              refine ⟨2666635424849485514012993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777756949899657009341995 2666635424849485514012993)
              ·
                refine ⟨1999976568637114135509745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666635424849485514012993 1999976568637114135509745)
                ·
                  refine ⟨1499982426477835601632309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1999976568637114135509745 1499982426477835601632309)
                  ·
                    refine ⟨140623352482297087653029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1499982426477835601632309 140623352482297087653029)
                    ·
                      rfl

theorem cell23_821589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_821589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821589 prefixEnd_821589 := by exact prefixLift 821589
  have htrace : WordTrace (prefixWord ++ tailWord_821589) baseStart_821589 baseEnd_821589 := by
    simpa [prefixWord, tailWord_821589, baseEnd_821589] using wordTrace_append hprefix tailTrace_821589
  have hstable : (prefixWord ++ tailWord_821589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821589).length < 2 ^ (prefixWord ++ tailWord_821589).sum := by decide
  have hdescent : baseEnd_821589 < baseStart_821589 := by decide
  rcases family_descends (prefixWord ++ tailWord_821589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821615 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 10]
def baseStart_821615 : Nat := 118140960795 + 821615 * 2 ^ 59
def prefixEnd_821615 : Nat := 4983230072969 + 3 ^ 40 * 821615 * 2
def baseEnd_821615 : Nat := 46875934215989795692663

theorem tailTrace_821615 : CollatzResearch.WordTrace tailWord_821615 prefixEnd_821615 46875934215989795692663 := by
  unfold tailWord_821615
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966760918436650515610299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19977840612291100343740199 29966760918436650515610299)
  ·
    refine ⟨44950141377654975773415449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29966760918436650515610299 44950141377654975773415449)
    ·
      refine ⟨33712606033241231830061587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44950141377654975773415449 33712606033241231830061587)
      ·
        refine ⟨50568909049861847745092381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33712606033241231830061587 50568909049861847745092381)
        ·
          refine ⟨18963340893698192904409643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50568909049861847745092381 18963340893698192904409643)
          ·
            refine ⟨28445011340547289356614465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18963340893698192904409643 28445011340547289356614465)
            ·
              refine ⟨21333758505410467017460849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28445011340547289356614465 21333758505410467017460849)
              ·
                refine ⟨16000318879057850263095637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21333758505410467017460849 16000318879057850263095637)
                ·
                  refine ⟨46875934215989795692663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16000318879057850263095637 46875934215989795692663)
                  ·
                    rfl

theorem cell23_821615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 10].length) (baseStart_821615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821615 prefixEnd_821615 := by exact prefixLift 821615
  have htrace : WordTrace (prefixWord ++ tailWord_821615) baseStart_821615 baseEnd_821615 := by
    simpa [prefixWord, tailWord_821615, baseEnd_821615] using wordTrace_append hprefix tailTrace_821615
  have hstable : (prefixWord ++ tailWord_821615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821615).length < 2 ^ (prefixWord ++ tailWord_821615).sum := by decide
  have hdescent : baseEnd_821615 < baseStart_821615 := by decide
  rcases family_descends (prefixWord ++ tailWord_821615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821629 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_821629 : Nat := 118140960795 + 821629 * 2 ^ 59
def prefixEnd_821629 : Nat := 4983230072969 + 3 ^ 40 * 821629 * 2
def baseEnd_821629 : Nat := 421890596673071106458903

theorem tailTrace_821629 : CollatzResearch.WordTrace tailWord_821629 prefixEnd_821629 421890596673071106458903 := by
  unfold tailWord_821629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967271540385930906619941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978181026923953937746627 29967271540385930906619941)
  ·
    refine ⟨5618863413822362044991239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29967271540385930906619941 5618863413822362044991239)
    ·
      refine ⟨8428295120733543067486859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618863413822362044991239 8428295120733543067486859)
      ·
        refine ⟨12642442681100314601230289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428295120733543067486859 12642442681100314601230289)
        ·
          refine ⟨9481832010825235950922717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12642442681100314601230289 9481832010825235950922717)
          ·
            refine ⟨3555687004059463481596019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9481832010825235950922717 3555687004059463481596019)
            ·
              refine ⟨5333530506089195222394029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555687004059463481596019 5333530506089195222394029)
              ·
                refine ⟨2000073939783448208397761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5333530506089195222394029 2000073939783448208397761)
                ·
                  refine ⟨1500055454837586156298321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2000073939783448208397761 1500055454837586156298321)
                  ·
                    refine ⟨1125041591128189617223741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1500055454837586156298321 1125041591128189617223741)
                    ·
                      refine ⟨421890596673071106458903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125041591128189617223741 421890596673071106458903)
                      ·
                        rfl

theorem cell23_821629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_821629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821629 prefixEnd_821629 := by exact prefixLift 821629
  have htrace : WordTrace (prefixWord ++ tailWord_821629) baseStart_821629 baseEnd_821629 := by
    simpa [prefixWord, tailWord_821629, baseEnd_821629] using wordTrace_append hprefix tailTrace_821629
  have hstable : (prefixWord ++ tailWord_821629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821629).length < 2 ^ (prefixWord ++ tailWord_821629).sum := by decide
  have hdescent : baseEnd_821629 < baseStart_821629 := by decide
  rcases family_descends (prefixWord ++ tailWord_821629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821636 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_821636 : Nat := 118140960795 + 821636 * 2 ^ 59
def prefixEnd_821636 : Nat := 4983230072969 + 3 ^ 40 * 821636 * 2
def baseEnd_821636 : Nat := 140631397012550859690457

theorem tailTrace_821636 : CollatzResearch.WordTrace tailWord_821636 prefixEnd_821636 140631397012550859690457 := by
  unfold tailWord_821636
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983763425680285551062381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19978351234240380734749841 14983763425680285551062381)
  ·
    refine ⟨5618911284630107081648393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14983763425680285551062381 5618911284630107081648393)
    ·
      refine ⟨4214183463472580311236295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5618911284630107081648393 4214183463472580311236295)
      ·
        refine ⟨6321275195208870466854443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214183463472580311236295 6321275195208870466854443)
        ·
          refine ⟨9481912792813305700281665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321275195208870466854443 9481912792813305700281665)
          ·
            refine ⟨7111434594609979275211249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9481912792813305700281665 7111434594609979275211249)
            ·
              refine ⟨5333575945957484456408437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7111434594609979275211249 5333575945957484456408437)
              ·
                refine ⟨500022744933514167788291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5333575945957484456408437 500022744933514167788291)
                ·
                  refine ⟨750034117400271251682437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500022744933514167788291 750034117400271251682437)
                  ·
                    refine ⟨140631397012550859690457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750034117400271251682437 140631397012550859690457)
                    ·
                      rfl

theorem cell23_821636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_821636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821636 prefixEnd_821636 := by exact prefixLift 821636
  have htrace : WordTrace (prefixWord ++ tailWord_821636) baseStart_821636 baseEnd_821636 := by
    simpa [prefixWord, tailWord_821636, baseEnd_821636] using wordTrace_append hprefix tailTrace_821636
  have hstable : (prefixWord ++ tailWord_821636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821636).length < 2 ^ (prefixWord ++ tailWord_821636).sum := by decide
  have hdescent : baseEnd_821636 < baseStart_821636 := by decide
  rcases family_descends (prefixWord ++ tailWord_821636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821646 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_821646 : Nat := 118140960795 + 821646 * 2 ^ 59
def prefixEnd_821646 : Nat := 4983230072969 + 3 ^ 40 * 821646 * 2
def baseEnd_821646 : Nat := 421899325844197539946325

theorem tailTrace_821646 : CollatzResearch.WordTrace tailWord_821646 prefixEnd_821646 421899325844197539946325 := by
  unfold tailWord_821646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745986447665542851248599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19978594387549561873325861 3745986447665542851248599)
  ·
    refine ⟨5618979671498314276872899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745986447665542851248599 5618979671498314276872899)
    ·
      refine ⟨8428469507247471415309349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618979671498314276872899 8428469507247471415309349)
      ·
        refine ⟨1580338032608900890370503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8428469507247471415309349 1580338032608900890370503)
        ·
          refine ⟨2370507048913351335555755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580338032608900890370503 2370507048913351335555755)
          ·
            refine ⟨3555760573370027003333633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370507048913351335555755 3555760573370027003333633)
            ·
              refine ⟨2666820430027520252500225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555760573370027003333633 2666820430027520252500225)
              ·
                refine ⟨2000115322520640189375169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666820430027520252500225 2000115322520640189375169)
                ·
                  refine ⟨1500086491890480142031377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2000115322520640189375169 1500086491890480142031377)
                  ·
                    refine ⟨1125064868917860106523533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1500086491890480142031377 1125064868917860106523533)
                    ·
                      refine ⟨421899325844197539946325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125064868917860106523533 421899325844197539946325)
                      ·
                        rfl

theorem cell23_821646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_821646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821646 prefixEnd_821646 := by exact prefixLift 821646
  have htrace : WordTrace (prefixWord ++ tailWord_821646) baseStart_821646 baseEnd_821646 := by
    simpa [prefixWord, tailWord_821646, baseEnd_821646] using wordTrace_append hprefix tailTrace_821646
  have hstable : (prefixWord ++ tailWord_821646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821646).length < 2 ^ (prefixWord ++ tailWord_821646).sum := by decide
  have hdescent : baseEnd_821646 < baseStart_821646 := by decide
  rcases family_descends (prefixWord ++ tailWord_821646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821669 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_821669 : Nat := 118140960795 + 821669 * 2 ^ 59
def prefixEnd_821669 : Nat := 4983230072969 + 3 ^ 40 * 821669 * 2
def baseEnd_821669 : Nat := 421911135899250949958719

theorem tailTrace_821669 : CollatzResearch.WordTrace tailWord_821669 prefixEnd_821669 421911135899250949958719 := by
  unfold tailWord_821669
  simp only [CollatzResearch.WordTrace]
  refine ⟨29968730460241017738076061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19979153640160678492050707 29968730460241017738076061)
  ·
    refine ⟨11238273922590381651778523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29968730460241017738076061 11238273922590381651778523)
    ·
      refine ⟨16857410883885572477667785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238273922590381651778523 16857410883885572477667785)
      ·
        refine ⟨12643058162914179358250839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16857410883885572477667785 12643058162914179358250839)
        ·
          refine ⟨18964587244371269037376259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643058162914179358250839 18964587244371269037376259)
          ·
            refine ⟨28446880866556903556064389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18964587244371269037376259 28446880866556903556064389)
            ·
              refine ⟨5333790162479419416762073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28446880866556903556064389 5333790162479419416762073)
              ·
                refine ⟨4000342621859564562571555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333790162479419416762073 4000342621859564562571555)
                ·
                  refine ⟨6000513932789346843857333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000342621859564562571555 6000513932789346843857333)
                  ·
                    refine ⟨562548181199001266611625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6000513932789346843857333 562548181199001266611625)
                    ·
                      refine ⟨421911135899250949958719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562548181199001266611625 421911135899250949958719)
                      ·
                        rfl

theorem cell23_821669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_821669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821669 prefixEnd_821669 := by exact prefixLift 821669
  have htrace : WordTrace (prefixWord ++ tailWord_821669) baseStart_821669 baseEnd_821669 := by
    simpa [prefixWord, tailWord_821669, baseEnd_821669] using wordTrace_append hprefix tailTrace_821669
  have hstable : (prefixWord ++ tailWord_821669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821669).length < 2 ^ (prefixWord ++ tailWord_821669).sum := by decide
  have hdescent : baseEnd_821669 < baseStart_821669 := by decide
  rcases family_descends (prefixWord ++ tailWord_821669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821693 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_821693 : Nat := 118140960795 + 821693 * 2 ^ 59
def prefixEnd_821693 : Nat := 4983230072969 + 3 ^ 40 * 821693 * 2
def baseEnd_821693 : Nat := 421923459434958856058609

theorem tailTrace_821693 : CollatzResearch.WordTrace tailWord_821693 prefixEnd_821693 421923459434958856058609 := by
  unfold tailWord_821693
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969605812154069836949733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19979737208102713224633155 29969605812154069836949733)
  ·
    refine ⟨5619301089778888094428075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29969605812154069836949733 5619301089778888094428075)
    ·
      refine ⟨8428951634668332141642113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619301089778888094428075 8428951634668332141642113)
      ·
        refine ⟨6321713726001249106231585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8428951634668332141642113 6321713726001249106231585)
        ·
          refine ⟨4741285294500936829673689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6321713726001249106231585 4741285294500936829673689)
          ·
            refine ⟨3555963970875702622255267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741285294500936829673689 3555963970875702622255267)
            ·
              refine ⟨5333945956313553933382901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555963970875702622255267 5333945956313553933382901)
              ·
                refine ⟨500057433404395681254647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5333945956313553933382901 500057433404395681254647)
                ·
                  refine ⟨750086150106593521881971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500057433404395681254647 750086150106593521881971)
                  ·
                    refine ⟨1125129225159890282822957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750086150106593521881971 1125129225159890282822957)
                    ·
                      refine ⟨421923459434958856058609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125129225159890282822957 421923459434958856058609)
                      ·
                        rfl

theorem cell23_821693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_821693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821693 prefixEnd_821693 := by exact prefixLift 821693
  have htrace : WordTrace (prefixWord ++ tailWord_821693) baseStart_821693 baseEnd_821693 := by
    simpa [prefixWord, tailWord_821693, baseEnd_821693] using wordTrace_append hprefix tailTrace_821693
  have hstable : (prefixWord ++ tailWord_821693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821693).length < 2 ^ (prefixWord ++ tailWord_821693).sum := by decide
  have hdescent : baseEnd_821693 < baseStart_821693 := by decide
  rcases family_descends (prefixWord ++ tailWord_821693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821722 : List Nat := [3, 1, 1, 2, 3, 1, 2, 10]
def baseStart_821722 : Nat := 118140960795 + 821722 * 2 ^ 59
def prefixEnd_821722 : Nat := 4983230072969 + 3 ^ 40 * 821722 * 2
def baseEnd_821722 : Nat := 15627346310145897873925

theorem tailTrace_821722 : CollatzResearch.WordTrace tailWord_821722 prefixEnd_821722 15627346310145897873925 := by
  unfold tailWord_821722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492665882262251947438855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19980442352699338526503613 7492665882262251947438855)
  ·
    refine ⟨11238998823393377921158283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7492665882262251947438855 11238998823393377921158283)
    ·
      refine ⟨16858498235090066881737425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238998823393377921158283 16858498235090066881737425)
      ·
        refine ⟨12643873676317550161303069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16858498235090066881737425 12643873676317550161303069)
        ·
          refine ⟨4741452628619081310488651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12643873676317550161303069 4741452628619081310488651)
          ·
            refine ⟨7112178942928621965732977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741452628619081310488651 7112178942928621965732977)
            ·
              refine ⟨5334134207196466474299733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112178942928621965732977 5334134207196466474299733)
              ·
                refine ⟨15627346310145897873925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5334134207196466474299733 15627346310145897873925)
                ·
                  rfl

theorem cell23_821722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_821722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821722 prefixEnd_821722 := by exact prefixLift 821722
  have htrace : WordTrace (prefixWord ++ tailWord_821722) baseStart_821722 baseEnd_821722 := by
    simpa [prefixWord, tailWord_821722, baseEnd_821722] using wordTrace_append hprefix tailTrace_821722
  have hstable : (prefixWord ++ tailWord_821722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821722).length < 2 ^ (prefixWord ++ tailWord_821722).sum := by decide
  have hdescent : baseEnd_821722 < baseStart_821722 := by decide
  rcases family_descends (prefixWord ++ tailWord_821722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821730 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_821730 : Nat := 118140960795 + 821730 * 2 ^ 59
def prefixEnd_821730 : Nat := 4983230072969 + 3 ^ 40 * 821730 * 2
def baseEnd_821730 : Nat := 140647486073058403765313

theorem tailTrace_821730 : CollatzResearch.WordTrace tailWord_821730 prefixEnd_821730 140647486073058403765313 := by
  unfold tailWord_821730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492738828255006289011661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19980636875346683437364429 7492738828255006289011661)
  ·
    refine ⟨2809777060595627358379373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7492738828255006289011661 2809777060595627358379373)
    ·
      refine ⟨1053666397723360259392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2809777060595627358379373 1053666397723360259392265)
      ·
        refine ⟨790249798292520194544199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1053666397723360259392265 790249798292520194544199)
        ·
          refine ⟨1185374697438780291816299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790249798292520194544199 1185374697438780291816299)
          ·
            refine ⟨1778062046158170437724449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185374697438780291816299 1778062046158170437724449)
            ·
              refine ⟨1333546534618627828293337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778062046158170437724449 1333546534618627828293337)
              ·
                refine ⟨1000159900963970871220003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333546534618627828293337 1000159900963970871220003)
                ·
                  refine ⟨1500239851445956306830005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000159900963970871220003 1500239851445956306830005)
                  ·
                    refine ⟨140647486073058403765313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1500239851445956306830005 140647486073058403765313)
                    ·
                      rfl

theorem cell23_821730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_821730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821730 prefixEnd_821730 := by exact prefixLift 821730
  have htrace : WordTrace (prefixWord ++ tailWord_821730) baseStart_821730 baseEnd_821730 := by
    simpa [prefixWord, tailWord_821730, baseEnd_821730] using wordTrace_append hprefix tailTrace_821730
  have hstable : (prefixWord ++ tailWord_821730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821730).length < 2 ^ (prefixWord ++ tailWord_821730).sum := by decide
  have hdescent : baseEnd_821730 < baseStart_821730 := by decide
  rcases family_descends (prefixWord ++ tailWord_821730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821733 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_821733 : Nat := 118140960795 + 821733 * 2 ^ 59
def prefixEnd_821733 : Nat := 4983230072969 + 3 ^ 40 * 821733 * 2
def baseEnd_821733 : Nat := 421943998661138699558425

theorem tailTrace_821733 : CollatzResearch.WordTrace tailWord_821733 prefixEnd_821733 421943998661138699558425 := by
  unfold tailWord_821733
  simp only [CollatzResearch.WordTrace]
  refine ⟨29971064732009156668405853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19980709821339437778937235 29971064732009156668405853)
  ·
    refine ⟨11239149274503433750652195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29971064732009156668405853 11239149274503433750652195)
    ·
      refine ⟨16858723911755150625978293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239149274503433750652195 16858723911755150625978293)
      ·
        refine ⟨1580505366727045371185465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16858723911755150625978293 1580505366727045371185465)
        ·
          refine ⟨1185379025045284028389099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580505366727045371185465 1185379025045284028389099)
          ·
            refine ⟨1778068537567926042583649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185379025045284028389099 1778068537567926042583649)
            ·
              refine ⟨1333551403175944531937737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778068537567926042583649 1333551403175944531937737)
              ·
                refine ⟨1000163552381958398953303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333551403175944531937737 1000163552381958398953303)
                ·
                  refine ⟨1500245328572937598429955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000163552381958398953303 1500245328572937598429955)
                  ·
                    refine ⟨2250367992859406397644933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1500245328572937598429955 2250367992859406397644933)
                    ·
                      refine ⟨421943998661138699558425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2250367992859406397644933 421943998661138699558425)
                      ·
                        rfl

theorem cell23_821733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_821733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821733 prefixEnd_821733 := by exact prefixLift 821733
  have htrace : WordTrace (prefixWord ++ tailWord_821733) baseStart_821733 baseEnd_821733 := by
    simpa [prefixWord, tailWord_821733, baseEnd_821733] using wordTrace_append hprefix tailTrace_821733
  have hstable : (prefixWord ++ tailWord_821733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821733).length < 2 ^ (prefixWord ++ tailWord_821733).sum := by decide
  have hdescent : baseEnd_821733 < baseStart_821733 := by decide
  rcases family_descends (prefixWord ++ tailWord_821733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821736 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_821736 : Nat := 118140960795 + 821736 * 2 ^ 59
def prefixEnd_821736 : Nat := 4983230072969 + 3 ^ 40 * 821736 * 2
def baseEnd_821736 : Nat := 421945539103102187820911

theorem tailTrace_821736 : CollatzResearch.WordTrace tailWord_821736 prefixEnd_821736 421945539103102187820911 := by
  unfold tailWord_821736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14985587075499144090382531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19980782767332192120510041 14985587075499144090382531)
  ·
    refine ⟨22478380613248716135573797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14985587075499144090382531 22478380613248716135573797)
    ·
      refine ⟨4214696364984134275420087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22478380613248716135573797 4214696364984134275420087)
      ·
        refine ⟨6322044547476201413130131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214696364984134275420087 6322044547476201413130131)
        ·
          refine ⟨9483066821214302119695197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322044547476201413130131 9483066821214302119695197)
          ·
            refine ⟨3556150057955363294885699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9483066821214302119695197 3556150057955363294885699)
            ·
              refine ⟨5334225086933044942328549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556150057955363294885699 5334225086933044942328549)
              ·
                refine ⟨1000167203799945926686603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5334225086933044942328549 1000167203799945926686603)
                ·
                  refine ⟨1500250805699918890029905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000167203799945926686603 1500250805699918890029905)
                  ·
                    refine ⟨1125188104274939167522429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1500250805699918890029905 1125188104274939167522429)
                    ·
                      refine ⟨421945539103102187820911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125188104274939167522429 421945539103102187820911)
                      ·
                        rfl

theorem cell23_821736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_821736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821736 prefixEnd_821736 := by exact prefixLift 821736
  have htrace : WordTrace (prefixWord ++ tailWord_821736) baseStart_821736 baseEnd_821736 := by
    simpa [prefixWord, tailWord_821736, baseEnd_821736] using wordTrace_append hprefix tailTrace_821736
  have hstable : (prefixWord ++ tailWord_821736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821736).length < 2 ^ (prefixWord ++ tailWord_821736).sum := by decide
  have hdescent : baseEnd_821736 < baseStart_821736 := by decide
  rcases family_descends (prefixWord ++ tailWord_821736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821767 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_821767 : Nat := 118140960795 + 821767 * 2 ^ 59
def prefixEnd_821767 : Nat := 4983230072969 + 3 ^ 40 * 821767 * 2
def baseEnd_821767 : Nat := 421961457003391566533269

theorem tailTrace_821767 : CollatzResearch.WordTrace tailWord_821767 prefixEnd_821767 421961457003391566533269 := by
  unfold tailWord_821767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972304813885980475143555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19981536542590653650095703 29972304813885980475143555)
  ·
    refine ⟨44958457220828970712715333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29972304813885980475143555 44958457220828970712715333)
    ·
      refine ⟨8429710728905432008634125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44958457220828970712715333 8429710728905432008634125)
      ·
        refine ⟨3161141523339537003237797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8429710728905432008634125 3161141523339537003237797)
        ·
          refine ⟨592714035626163188107087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3161141523339537003237797 592714035626163188107087)
          ·
            refine ⟨889071053439244782160631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592714035626163188107087 889071053439244782160631)
            ·
              refine ⟨1333606580158867173240947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889071053439244782160631 1333606580158867173240947)
              ·
                refine ⟨2000409870238300759861421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333606580158867173240947 2000409870238300759861421)
                ·
                  refine ⟨750153701339362784948033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2000409870238300759861421 750153701339362784948033)
                  ·
                    refine ⟨562615276004522088711025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750153701339362784948033 562615276004522088711025)
                    ·
                      refine ⟨421961457003391566533269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562615276004522088711025 421961457003391566533269)
                      ·
                        rfl

theorem cell23_821767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_821767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821767 prefixEnd_821767 := by exact prefixLift 821767
  have htrace : WordTrace (prefixWord ++ tailWord_821767) baseStart_821767 baseEnd_821767 := by
    simpa [prefixWord, tailWord_821767, baseEnd_821767] using wordTrace_append hprefix tailTrace_821767
  have hstable : (prefixWord ++ tailWord_821767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821767).length < 2 ^ (prefixWord ++ tailWord_821767).sum := by decide
  have hdescent : baseEnd_821767 < baseStart_821767 := by decide
  rcases family_descends (prefixWord ++ tailWord_821767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821773 : List Nat := [1, 7, 1, 1, 1, 2, 2, 8]
def baseStart_821773 : Nat := 118140960795 + 821773 * 2 ^ 59
def prefixEnd_821773 : Nat := 4983230072969 + 3 ^ 40 * 821773 * 2
def baseEnd_821773 : Nat := 15628316218048834928083

theorem tailTrace_821773 : CollatzResearch.WordTrace tailWord_821773 prefixEnd_821773 15628316218048834928083 := by
  unfold tailWord_821773
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972523651864243499861973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19981682434576162333241315 29972523651864243499861973)
  ·
    refine ⟨702481023090568207028015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29972523651864243499861973 702481023090568207028015)
    ·
      refine ⟨1053721534635852310542023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702481023090568207028015 1053721534635852310542023)
      ·
        refine ⟨1580582301953778465813035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053721534635852310542023 1580582301953778465813035)
        ·
          refine ⟨2370873452930667698719553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580582301953778465813035 2370873452930667698719553)
          ·
            refine ⟨1778155089698000774039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370873452930667698719553 1778155089698000774039665)
            ·
              refine ⟨1333616317273500580529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778155089698000774039665 1333616317273500580529749)
              ·
                refine ⟨15628316218048834928083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1333616317273500580529749 15628316218048834928083)
                ·
                  rfl

theorem cell23_821773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 8].length) (baseStart_821773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821773 prefixEnd_821773 := by exact prefixLift 821773
  have htrace : WordTrace (prefixWord ++ tailWord_821773) baseStart_821773 baseEnd_821773 := by
    simpa [prefixWord, tailWord_821773, baseEnd_821773] using wordTrace_append hprefix tailTrace_821773
  have hstable : (prefixWord ++ tailWord_821773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821773).length < 2 ^ (prefixWord ++ tailWord_821773).sum := by decide
  have hdescent : baseEnd_821773 < baseStart_821773 := by decide
  rcases family_descends (prefixWord ++ tailWord_821773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821809 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_821809 : Nat := 118140960795 + 821809 * 2 ^ 59
def prefixEnd_821809 : Nat := 4983230072969 + 3 ^ 40 * 821809 * 2
def baseEnd_821809 : Nat := 421983023190880402208075

theorem tailTrace_821809 : CollatzResearch.WordTrace tailWord_821809 prefixEnd_821809 421983023190880402208075 := by
  unfold tailWord_821809
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973836679733821648172481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19982557786489214432114987 29973836679733821648172481)
  ·
    refine ⟨22480377509800366236129361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29973836679733821648172481 22480377509800366236129361)
    ·
      refine ⟨16860283132350274677097021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22480377509800366236129361 16860283132350274677097021)
      ·
        refine ⟨6322606174631353003911383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16860283132350274677097021 6322606174631353003911383)
        ·
          refine ⟨9483909261947029505867075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322606174631353003911383 9483909261947029505867075)
          ·
            refine ⟨14225863892920544258800613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483909261947029505867075 14225863892920544258800613)
            ·
              refine ⟨2667349479922602048525115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14225863892920544258800613 2667349479922602048525115)
              ·
                refine ⟨4001024219883903072787673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667349479922602048525115 4001024219883903072787673)
                ·
                  refine ⟨3000768164912927304590755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001024219883903072787673 3000768164912927304590755)
                  ·
                    refine ⟨4501152247369390956886133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000768164912927304590755 4501152247369390956886133)
                    ·
                      refine ⟨421983023190880402208075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4501152247369390956886133 421983023190880402208075)
                      ·
                        rfl

theorem cell23_821809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_821809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821809 prefixEnd_821809 := by exact prefixLift 821809
  have htrace : WordTrace (prefixWord ++ tailWord_821809) baseStart_821809 baseEnd_821809 := by
    simpa [prefixWord, tailWord_821809, baseEnd_821809] using wordTrace_append hprefix tailTrace_821809
  have hstable : (prefixWord ++ tailWord_821809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821809).length < 2 ^ (prefixWord ++ tailWord_821809).sum := by decide
  have hdescent : baseEnd_821809 < baseStart_821809 := by decide
  rcases family_descends (prefixWord ++ tailWord_821809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821839 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_821839 : Nat := 118140960795 + 821839 * 2 ^ 59
def prefixEnd_821839 : Nat := 4983230072969 + 3 ^ 40 * 821839 * 2
def baseEnd_821839 : Nat := 421998427610515284832937

theorem tailTrace_821839 : CollatzResearch.WordTrace tailWord_821839 prefixEnd_821839 421998427610515284832937 := by
  unfold tailWord_821839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974930869625136771764571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19983287246416757847843047 29974930869625136771764571)
  ·
    refine ⟨44962396304437705157646857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29974930869625136771764571 44962396304437705157646857)
    ·
      refine ⟨33721797228328278868235143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44962396304437705157646857 33721797228328278868235143)
      ·
        refine ⟨50582695842492418302352715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33721797228328278868235143 50582695842492418302352715)
        ·
          refine ⟨75874043763738627453529073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50582695842492418302352715 75874043763738627453529073)
          ·
            refine ⟨56905532822803970590146805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75874043763738627453529073 56905532822803970590146805)
            ·
              refine ⟨5334893702137872242826263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56905532822803970590146805 5334893702137872242826263)
              ·
                refine ⟨8002340553206808364239395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334893702137872242826263 8002340553206808364239395)
                ·
                  refine ⟨12003510829810212546359093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002340553206808364239395 12003510829810212546359093)
                  ·
                    refine ⟨1125329140294707426221165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12003510829810212546359093 1125329140294707426221165)
                    ·
                      refine ⟨421998427610515284832937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125329140294707426221165 421998427610515284832937)
                      ·
                        rfl

theorem cell23_821839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_821839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821839 prefixEnd_821839 := by exact prefixLift 821839
  have htrace : WordTrace (prefixWord ++ tailWord_821839) baseStart_821839 baseEnd_821839 := by
    simpa [prefixWord, tailWord_821839, baseEnd_821839] using wordTrace_append hprefix tailTrace_821839
  have hstable : (prefixWord ++ tailWord_821839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821839).length < 2 ^ (prefixWord ++ tailWord_821839).sum := by decide
  have hdescent : baseEnd_821839 < baseStart_821839 := by decide
  rcases family_descends (prefixWord ++ tailWord_821839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821859 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 7]
def baseStart_821859 : Nat := 118140960795 + 821859 * 2 ^ 59
def prefixEnd_821859 : Nat := 4983230072969 + 3 ^ 40 * 821859 * 2
def baseEnd_821859 : Nat := 140669565741201735527615

theorem tailTrace_821859 : CollatzResearch.WordTrace tailWord_821859 prefixEnd_821859 140669565741201735527615 := by
  unfold tailWord_821859
  simp only [CollatzResearch.WordTrace]
  refine ⟨29975660329552680187492631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19983773553035120124995087 29975660329552680187492631)
  ·
    refine ⟨44963490494329020281238947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29975660329552680187492631 44963490494329020281238947)
    ·
      refine ⟨67445235741493530421858421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44963490494329020281238947 67445235741493530421858421)
      ·
        refine ⟨6322990850765018477049227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67445235741493530421858421 6322990850765018477049227)
        ·
          refine ⟨9484486276147527715573841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322990850765018477049227 9484486276147527715573841)
          ·
            refine ⟨7113364707110645786680381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9484486276147527715573841 7113364707110645786680381)
            ·
              refine ⟨2667511765166492170005143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7113364707110645786680381 2667511765166492170005143)
              ·
                refine ⟨4001267647749738255007715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667511765166492170005143 4001267647749738255007715)
                ·
                  refine ⟨6001901471624607382511573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001267647749738255007715 6001901471624607382511573)
                  ·
                    refine ⟨140669565741201735527615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6001901471624607382511573 140669565741201735527615)
                    ·
                      rfl

theorem cell23_821859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_821859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821859 prefixEnd_821859 := by exact prefixLift 821859
  have htrace : WordTrace (prefixWord ++ tailWord_821859) baseStart_821859 baseEnd_821859 := by
    simpa [prefixWord, tailWord_821859, baseEnd_821859] using wordTrace_append hprefix tailTrace_821859
  have hstable : (prefixWord ++ tailWord_821859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821859).length < 2 ^ (prefixWord ++ tailWord_821859).sum := by decide
  have hdescent : baseEnd_821859 < baseStart_821859 := by decide
  rcases family_descends (prefixWord ++ tailWord_821859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821874 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_821874 : Nat := 118140960795 + 821874 * 2 ^ 59
def prefixEnd_821874 : Nat := 4983230072969 + 3 ^ 40 * 821874 * 2
def baseEnd_821874 : Nat := 422016399433422647895277

theorem tailTrace_821874 : CollatzResearch.WordTrace tailWord_821874 prefixEnd_821874 422016399433422647895277 := by
  unfold tailWord_821874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494051856124584437322169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19984138282998891832859117 7494051856124584437322169)
  ·
    refine ⟨5620538892093438327991627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7494051856124584437322169 5620538892093438327991627)
    ·
      refine ⟨8430808338140157491987441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5620538892093438327991627 8430808338140157491987441)
      ·
        refine ⟨6323106253605118118990581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8430808338140157491987441 6323106253605118118990581)
        ·
          refine ⟨592791211275479823655367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6323106253605118118990581 592791211275479823655367)
          ·
            refine ⟨889186816913219735483051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592791211275479823655367 889186816913219735483051)
            ·
              refine ⟨1333780225369829603224577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889186816913219735483051 1333780225369829603224577)
              ·
                refine ⟨1000335169027372202418433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333780225369829603224577 1000335169027372202418433)
                ·
                  refine ⟨750251376770529151813825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000335169027372202418433 750251376770529151813825)
                  ·
                    refine ⟨562688532577896863860369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750251376770529151813825 562688532577896863860369)
                    ·
                      refine ⟨422016399433422647895277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562688532577896863860369 422016399433422647895277)
                      ·
                        rfl

theorem cell23_821874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_821874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821874 prefixEnd_821874 := by exact prefixLift 821874
  have htrace : WordTrace (prefixWord ++ tailWord_821874) baseStart_821874 baseEnd_821874 := by
    simpa [prefixWord, tailWord_821874, baseEnd_821874] using wordTrace_append hprefix tailTrace_821874
  have hstable : (prefixWord ++ tailWord_821874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821874).length < 2 ^ (prefixWord ++ tailWord_821874).sum := by decide
  have hdescent : baseEnd_821874 < baseStart_821874 := by decide
  rcases family_descends (prefixWord ++ tailWord_821874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821923 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 1, 4]
def baseStart_821923 : Nat := 118140960795 + 821923 * 2 ^ 59
def prefixEnd_821923 : Nat := 4983230072969 + 3 ^ 40 * 821923 * 2
def baseEnd_821923 : Nat := 140680519995164318727517

theorem tailTrace_821923 : CollatzResearch.WordTrace tailWord_821923 prefixEnd_821923 140680519995164318727517 := by
  unfold tailWord_821923
  simp only [CollatzResearch.WordTrace]
  refine ⟨29977994601320819117822423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985329734213879411881615 29977994601320819117822423)
  ·
    refine ⟨44966991901981228676733635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29977994601320819117822423 44966991901981228676733635)
    ·
      refine ⟨67450487852971843015100453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44966991901981228676733635 67450487852971843015100453)
      ·
        refine ⟨12646966472432220565331335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67450487852971843015100453 12646966472432220565331335)
        ·
          refine ⟨18970449708648330847997003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646966472432220565331335 18970449708648330847997003)
          ·
            refine ⟨28455674562972496271995505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970449708648330847997003 28455674562972496271995505)
            ·
              refine ⟨21341755922229372203996629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28455674562972496271995505 21341755922229372203996629)
              ·
                refine ⟨500197404427250911031171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21341755922229372203996629 500197404427250911031171)
                ·
                  refine ⟨750296106640876366546757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500197404427250911031171 750296106640876366546757)
                  ·
                    refine ⟨140680519995164318727517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750296106640876366546757 140680519995164318727517)
                    ·
                      rfl

theorem cell23_821923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 4].length) (baseStart_821923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821923 prefixEnd_821923 := by exact prefixLift 821923
  have htrace : WordTrace (prefixWord ++ tailWord_821923) baseStart_821923 baseEnd_821923 := by
    simpa [prefixWord, tailWord_821923, baseEnd_821923] using wordTrace_append hprefix tailTrace_821923
  have hstable : (prefixWord ++ tailWord_821923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821923).length < 2 ^ (prefixWord ++ tailWord_821923).sum := by decide
  have hdescent : baseEnd_821923 < baseStart_821923 := by decide
  rcases family_descends (prefixWord ++ tailWord_821923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821933 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_821933 : Nat := 118140960795 + 821933 * 2 ^ 59
def prefixEnd_821933 : Nat := 4983230072969 + 3 ^ 40 * 821933 * 2
def baseEnd_821933 : Nat := 422046694792037917057505

theorem tailTrace_821933 : CollatzResearch.WordTrace tailWord_821933 prefixEnd_821933 422046694792037917057505 := by
  unfold tailWord_821933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978359331284590825686453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985572887523060550457635 29978359331284590825686453)
  ·
    refine ⟨2810471187307930389908105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29978359331284590825686453 2810471187307930389908105)
    ·
      refine ⟨2107853390480947792431079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2810471187307930389908105 2107853390480947792431079)
      ·
        refine ⟨3161780085721421688646619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107853390480947792431079 3161780085721421688646619)
        ·
          refine ⟨4742670128582132532969929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161780085721421688646619 4742670128582132532969929)
          ·
            refine ⟨3557002596436599399727447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4742670128582132532969929 3557002596436599399727447)
            ·
              refine ⟨5335503894654899099591171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557002596436599399727447 5335503894654899099591171)
              ·
                refine ⟨8003255841982348649386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335503894654899099591171 8003255841982348649386757)
                ·
                  refine ⟨1500610470371690371760017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8003255841982348649386757 1500610470371690371760017)
                  ·
                    refine ⟨1125457852778767778820013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1500610470371690371760017 1125457852778767778820013)
                    ·
                      refine ⟨422046694792037917057505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125457852778767778820013 422046694792037917057505)
                      ·
                        rfl

theorem cell23_821933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_821933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821933 prefixEnd_821933 := by exact prefixLift 821933
  have htrace : WordTrace (prefixWord ++ tailWord_821933) baseStart_821933 baseEnd_821933 := by
    simpa [prefixWord, tailWord_821933, baseEnd_821933] using wordTrace_append hprefix tailTrace_821933
  have hstable : (prefixWord ++ tailWord_821933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821933).length < 2 ^ (prefixWord ++ tailWord_821933).sum := by decide
  have hdescent : baseEnd_821933 < baseStart_821933 := by decide
  rcases family_descends (prefixWord ++ tailWord_821933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821959 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_821959 : Nat := 118140960795 + 821959 * 2 ^ 59
def prefixEnd_821959 : Nat := 4983230072969 + 3 ^ 40 * 821959 * 2
def baseEnd_821959 : Nat := 422060045289054815332385

theorem tailTrace_821959 : CollatzResearch.WordTrace tailWord_821959 prefixEnd_821959 422060045289054815332385 := by
  unfold tailWord_821959
  simp only [CollatzResearch.WordTrace]
  refine ⟨29979307629190397266132931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19986205086126931510755287 29979307629190397266132931)
  ·
    refine ⟨44968961443785595899199397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29979307629190397266132931 44968961443785595899199397)
    ·
      refine ⟨8431680270709799231099887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44968961443785595899199397 8431680270709799231099887)
      ·
        refine ⟨12647520406064698846649831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431680270709799231099887 12647520406064698846649831)
        ·
          refine ⟨18971280609097048269974747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647520406064698846649831 18971280609097048269974747)
          ·
            refine ⟨28456920913645572404962121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18971280609097048269974747 28456920913645572404962121)
            ·
              refine ⟨21342690685234179303721591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28456920913645572404962121 21342690685234179303721591)
              ·
                refine ⟨32014036027851268955582387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21342690685234179303721591 32014036027851268955582387)
                ·
                  refine ⟨48021054041776903433373581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32014036027851268955582387 48021054041776903433373581)
                  ·
                    refine ⟨18007895265666338787515093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48021054041776903433373581 18007895265666338787515093)
                    ·
                      refine ⟨422060045289054815332385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18007895265666338787515093 422060045289054815332385)
                      ·
                        rfl

theorem cell23_821959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_821959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821959 prefixEnd_821959 := by exact prefixLift 821959
  have htrace : WordTrace (prefixWord ++ tailWord_821959) baseStart_821959 baseEnd_821959 := by
    simpa [prefixWord, tailWord_821959, baseEnd_821959] using wordTrace_append hprefix tailTrace_821959
  have hstable : (prefixWord ++ tailWord_821959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821959).length < 2 ^ (prefixWord ++ tailWord_821959).sum := by decide
  have hdescent : baseEnd_821959 < baseStart_821959 := by decide
  rcases family_descends (prefixWord ++ tailWord_821959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821997 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_821997 : Nat := 118140960795 + 821997 * 2 ^ 59
def prefixEnd_821997 : Nat := 4983230072969 + 3 ^ 40 * 821997 * 2
def baseEnd_821997 : Nat := 422079557553925666657211

theorem tailTrace_821997 : CollatzResearch.WordTrace tailWord_821997 prefixEnd_821997 422079557553925666657211 := by
  unfold tailWord_821997
  simp only [CollatzResearch.WordTrace]
  refine ⟨29980693603052729756016245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19987129068701819837344163 29980693603052729756016245)
  ·
    refine ⟨2810690025286193414626523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29980693603052729756016245 2810690025286193414626523)
    ·
      refine ⟨4216035037929290121939785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810690025286193414626523 4216035037929290121939785)
      ·
        refine ⟨3162026278446967591454839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4216035037929290121939785 3162026278446967591454839)
        ·
          refine ⟨4743039417670451387182259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162026278446967591454839 4743039417670451387182259)
          ·
            refine ⟨7114559126505677080773389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743039417670451387182259 7114559126505677080773389)
            ·
              refine ⟨2667959672439628905290021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7114559126505677080773389 2667959672439628905290021)
              ·
                refine ⟨500242438582430419741879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2667959672439628905290021 500242438582430419741879)
                ·
                  refine ⟨750363657873645629612819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500242438582430419741879 750363657873645629612819)
                  ·
                    refine ⟨1125545486810468444419229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750363657873645629612819 1125545486810468444419229)
                    ·
                      refine ⟨422079557553925666657211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125545486810468444419229 422079557553925666657211)
                      ·
                        rfl

theorem cell23_821997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_821997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_821997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_821997 prefixEnd_821997 := by exact prefixLift 821997
  have htrace : WordTrace (prefixWord ++ tailWord_821997) baseStart_821997 baseEnd_821997 := by
    simpa [prefixWord, tailWord_821997, baseEnd_821997] using wordTrace_append hprefix tailTrace_821997
  have hstable : (prefixWord ++ tailWord_821997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821997).length < 2 ^ (prefixWord ++ tailWord_821997).sum := by decide
  have hdescent : baseEnd_821997 < baseStart_821997 := by decide
  rcases family_descends (prefixWord ++ tailWord_821997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822013 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_822013 : Nat := 118140960795 + 822013 * 2 ^ 59
def prefixEnd_822013 : Nat := 4983230072969 + 3 ^ 40 * 822013 * 2
def baseEnd_822013 : Nat := 140695924414799201352379

theorem tailTrace_822013 : CollatzResearch.WordTrace tailWord_822013 prefixEnd_822013 140695924414799201352379 := by
  unfold tailWord_822013
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981277170994764488598693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19987518113996509659065795 29981277170994764488598693)
  ·
    refine ⟨5621489469561518341612255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29981277170994764488598693 5621489469561518341612255)
    ·
      refine ⟨8432234204342277512418383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621489469561518341612255 8432234204342277512418383)
      ·
        refine ⟨12648351306513416268627575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8432234204342277512418383 12648351306513416268627575)
        ·
          refine ⟨18972526959770124402941363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12648351306513416268627575 18972526959770124402941363)
          ·
            refine ⟨28458790439655186604412045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18972526959770124402941363 28458790439655186604412045)
            ·
              refine ⟨10672046414870694976654517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28458790439655186604412045 10672046414870694976654517)
              ·
                refine ⟨1000504351394127654061361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10672046414870694976654517 1000504351394127654061361)
                ·
                  refine ⟨750378263545595740546021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000504351394127654061361 750378263545595740546021)
                  ·
                    refine ⟨140695924414799201352379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750378263545595740546021 140695924414799201352379)
                    ·
                      rfl

theorem cell23_822013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_822013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822013 prefixEnd_822013 := by exact prefixLift 822013
  have htrace : WordTrace (prefixWord ++ tailWord_822013) baseStart_822013 baseEnd_822013 := by
    simpa [prefixWord, tailWord_822013, baseEnd_822013] using wordTrace_append hprefix tailTrace_822013
  have hstable : (prefixWord ++ tailWord_822013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822013).length < 2 ^ (prefixWord ++ tailWord_822013).sum := by decide
  have hdescent : baseEnd_822013 < baseStart_822013 := by decide
  rcases family_descends (prefixWord ++ tailWord_822013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822034 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_822034 : Nat := 118140960795 + 822034 * 2 ^ 59
def prefixEnd_822034 : Nat := 4983230072969 + 3 ^ 40 * 822034 * 2
def baseEnd_822034 : Nat := 140699518779380673964847

theorem tailTrace_822034 : CollatzResearch.WordTrace tailWord_822034 prefixEnd_822034 140699518779380673964847 := by
  unfold tailWord_822034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495510775979671268778289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19988028735945790050075437 7495510775979671268778289)
  ·
    refine ⟨5621633081984753451583717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7495510775979671268778289 5621633081984753451583717)
    ·
      refine ⟨1054056202872141272171947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5621633081984753451583717 1054056202872141272171947)
      ·
        refine ⟨1581084304308211908257921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054056202872141272171947 1581084304308211908257921)
        ·
          refine ⟨1185813228231158931193441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581084304308211908257921 1185813228231158931193441)
          ·
            refine ⟨889359921173369198395081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185813228231158931193441 889359921173369198395081)
            ·
              refine ⟨667019940880026898796311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889359921173369198395081 667019940880026898796311)
              ·
                refine ⟨1000529911320040348194467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667019940880026898796311 1000529911320040348194467)
                ·
                  refine ⟨1500794866980060522291701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000529911320040348194467 1500794866980060522291701)
                  ·
                    refine ⟨140699518779380673964847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1500794866980060522291701 140699518779380673964847)
                    ·
                      rfl

theorem cell23_822034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_822034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822034 prefixEnd_822034 := by exact prefixLift 822034
  have htrace : WordTrace (prefixWord ++ tailWord_822034) baseStart_822034 baseEnd_822034 := by
    simpa [prefixWord, tailWord_822034, baseEnd_822034] using wordTrace_append hprefix tailTrace_822034
  have hstable : (prefixWord ++ tailWord_822034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822034).length < 2 ^ (prefixWord ++ tailWord_822034).sum := by decide
  have hdescent : baseEnd_822034 < baseStart_822034 := by decide
  rcases family_descends (prefixWord ++ tailWord_822034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822077 : List Nat := [1, 4, 1, 4, 3, 1, 2, 7]
def baseStart_822077 : Nat := 118140960795 + 822077 * 2 ^ 59
def prefixEnd_822077 : Nat := 4983230072969 + 3 ^ 40 * 822077 * 2
def baseEnd_822077 : Nat := 15634097629862420505809

theorem tailTrace_822077 : CollatzResearch.WordTrace tailWord_822077 prefixEnd_822077 15634097629862420505809 := by
  unfold tailWord_822077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29983611442762903418928485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19989074295175268945952323 29983611442762903418928485)
  ·
    refine ⟨5621927145518044391049091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29983611442762903418928485 5621927145518044391049091)
    ·
      refine ⟨8432890718277066586573637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621927145518044391049091 8432890718277066586573637)
      ·
        refine ⟨1581167009676949984982557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8432890718277066586573637 1581167009676949984982557)
        ·
          refine ⟨592937628628856244368459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1581167009676949984982557 592937628628856244368459)
          ·
            refine ⟨889406442943284366552689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592937628628856244368459 889406442943284366552689)
            ·
              refine ⟨667054832207463274914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889406442943284366552689 667054832207463274914517)
              ·
                refine ⟨15634097629862420505809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 667054832207463274914517 15634097629862420505809)
                ·
                  rfl

theorem cell23_822077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 7].length) (baseStart_822077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822077 prefixEnd_822077 := by exact prefixLift 822077
  have htrace : WordTrace (prefixWord ++ tailWord_822077) baseStart_822077 baseEnd_822077 := by
    simpa [prefixWord, tailWord_822077, baseEnd_822077] using wordTrace_append hprefix tailTrace_822077
  have hstable : (prefixWord ++ tailWord_822077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822077).length < 2 ^ (prefixWord ++ tailWord_822077).sum := by decide
  have hdescent : baseEnd_822077 < baseStart_822077 := by decide
  rcases family_descends (prefixWord ++ tailWord_822077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822096 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_822096 : Nat := 118140960795 + 822096 * 2 ^ 59
def prefixEnd_822096 : Nat := 4983230072969 + 3 ^ 40 * 822096 * 2
def baseEnd_822096 : Nat := 422130392138720779319255

theorem tailTrace_822096 : CollatzResearch.WordTrace tailWord_822096 prefixEnd_822096 422130392138720779319255 := by
  unfold tailWord_822096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14992152214847034831935071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19989536286462713109246761 14992152214847034831935071)
  ·
    refine ⟨22488228322270552247902607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14992152214847034831935071 22488228322270552247902607)
    ·
      refine ⟨33732342483405828371853911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22488228322270552247902607 33732342483405828371853911)
      ·
        refine ⟨50598513725108742557780867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33732342483405828371853911 50598513725108742557780867)
        ·
          refine ⟨75897770587663113836671301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50598513725108742557780867 75897770587663113836671301)
          ·
            refine ⟨14230831985186833844375869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75897770587663113836671301 14230831985186833844375869)
            ·
              refine ⟨5336561994445062691640951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14230831985186833844375869 5336561994445062691640951)
              ·
                refine ⟨8004842991667594037461427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336561994445062691640951 8004842991667594037461427)
                ·
                  refine ⟨12007264487501391056192141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004842991667594037461427 12007264487501391056192141)
                  ·
                    refine ⟨4502724182813021646072053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12007264487501391056192141 4502724182813021646072053)
                    ·
                      refine ⟨422130392138720779319255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4502724182813021646072053 422130392138720779319255)
                      ·
                        rfl

theorem cell23_822096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_822096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822096 prefixEnd_822096 := by exact prefixLift 822096
  have htrace : WordTrace (prefixWord ++ tailWord_822096) baseStart_822096 baseEnd_822096 := by
    simpa [prefixWord, tailWord_822096, baseEnd_822096] using wordTrace_append hprefix tailTrace_822096
  have hstable : (prefixWord ++ tailWord_822096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822096).length < 2 ^ (prefixWord ++ tailWord_822096).sum := by decide
  have hdescent : baseEnd_822096 < baseStart_822096 := by decide
  rcases family_descends (prefixWord ++ tailWord_822096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822173 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_822173 : Nat := 118140960795 + 822173 * 2 ^ 59
def prefixEnd_822173 : Nat := 4983230072969 + 3 ^ 40 * 822173 * 2
def baseEnd_822173 : Nat := 422169930149116978056401

theorem tailTrace_822173 : CollatzResearch.WordTrace tailWord_822173 prefixEnd_822173 422169930149116978056401 := by
  unfold tailWord_822173
  simp only [CollatzResearch.WordTrace]
  refine ⟨29987112850415111814423173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19991408566943407876282115 29987112850415111814423173)
  ·
    refine ⟨5622583659452833465204345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29987112850415111814423173 5622583659452833465204345)
    ·
      refine ⟨4216937744589625098903259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5622583659452833465204345 4216937744589625098903259)
      ·
        refine ⟨6325406616884437648354889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216937744589625098903259 6325406616884437648354889)
        ·
          refine ⟨4744054962663328236266167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6325406616884437648354889 4744054962663328236266167)
          ·
            refine ⟨7116082443994992354399251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744054962663328236266167 7116082443994992354399251)
            ·
              refine ⟨10674123665992488531598877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116082443994992354399251 10674123665992488531598877)
              ·
                refine ⟨4002796374747183199349579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10674123665992488531598877 4002796374747183199349579)
                ·
                  refine ⟨6004194562120774799024369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002796374747183199349579 6004194562120774799024369)
                  ·
                    refine ⟨4503145921590581099268277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6004194562120774799024369 4503145921590581099268277)
                    ·
                      refine ⟨422169930149116978056401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4503145921590581099268277 422169930149116978056401)
                      ·
                        rfl

theorem cell23_822173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_822173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822173 prefixEnd_822173 := by exact prefixLift 822173
  have htrace : WordTrace (prefixWord ++ tailWord_822173) baseStart_822173 baseEnd_822173 := by
    simpa [prefixWord, tailWord_822173, baseEnd_822173] using wordTrace_append hprefix tailTrace_822173
  have hstable : (prefixWord ++ tailWord_822173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822173).length < 2 ^ (prefixWord ++ tailWord_822173).sum := by decide
  have hdescent : baseEnd_822173 < baseStart_822173 := by decide
  rcases family_descends (prefixWord ++ tailWord_822173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822200 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_822200 : Nat := 118140960795 + 822200 * 2 ^ 59
def prefixEnd_822200 : Nat := 4983230072969 + 3 ^ 40 * 822200 * 2
def baseEnd_822200 : Nat := 422183794126788372418777

theorem tailTrace_822200 : CollatzResearch.WordTrace tailWord_822200 prefixEnd_822200 422183794126788372418777 := by
  unfold tailWord_822200
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994048810658647712828027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19992065080878196950437369 14994048810658647712828027)
  ·
    refine ⟨22491073215987971569242041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14994048810658647712828027 22491073215987971569242041)
    ·
      refine ⟨16868304911990978676931531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22491073215987971569242041 16868304911990978676931531)
      ·
        refine ⟨25302457367986468015397297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16868304911990978676931531 25302457367986468015397297)
        ·
          refine ⟨18976843025989851011547973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25302457367986468015397297 18976843025989851011547973)
          ·
            refine ⟨3558158067373097064665245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18976843025989851011547973 3558158067373097064665245)
            ·
              refine ⟨1334309275264911399249467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558158067373097064665245 1334309275264911399249467)
              ·
                refine ⟨2001463912897367098874201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334309275264911399249467 2001463912897367098874201)
                ·
                  refine ⟨1501097934673025324155651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001463912897367098874201 1501097934673025324155651)
                  ·
                    refine ⟨2251646902009537986233477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501097934673025324155651 2251646902009537986233477)
                    ·
                      refine ⟨422183794126788372418777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2251646902009537986233477 422183794126788372418777)
                      ·
                        rfl

theorem cell23_822200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_822200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822200 prefixEnd_822200 := by exact prefixLift 822200
  have htrace : WordTrace (prefixWord ++ tailWord_822200) baseStart_822200 baseEnd_822200 := by
    simpa [prefixWord, tailWord_822200, baseEnd_822200] using wordTrace_append hprefix tailTrace_822200
  have hstable : (prefixWord ++ tailWord_822200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822200).length < 2 ^ (prefixWord ++ tailWord_822200).sum := by decide
  have hdescent : baseEnd_822200 < baseStart_822200 := by decide
  rcases family_descends (prefixWord ++ tailWord_822200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822220 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_822220 : Nat := 118140960795 + 822220 * 2 ^ 59
def prefixEnd_822220 : Nat := 4983230072969 + 3 ^ 40 * 822220 * 2
def baseEnd_822220 : Nat := 422194063739878294168685

theorem tailTrace_822220 : CollatzResearch.WordTrace tailWord_822220 prefixEnd_822220 422194063739878294168685 := by
  unfold tailWord_822220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994413540622419420692057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19992551387496559227589409 14994413540622419420692057)
  ·
    refine ⟨11245810155466814565519043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14994413540622419420692057 11245810155466814565519043)
    ·
      refine ⟨16868715233200221848278565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11245810155466814565519043 16868715233200221848278565)
      ·
        refine ⟨3162884106225041596552231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16868715233200221848278565 3162884106225041596552231)
        ·
          refine ⟨4744326159337562394828347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162884106225041596552231 4744326159337562394828347)
          ·
            refine ⟨7116489239006343592242521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744326159337562394828347 7116489239006343592242521)
            ·
              refine ⟨5337366929254757694181891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116489239006343592242521 5337366929254757694181891)
              ·
                refine ⟨8006050393882136541272837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337366929254757694181891 8006050393882136541272837)
                ·
                  refine ⟨1501134448852900601488657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8006050393882136541272837 1501134448852900601488657)
                  ·
                    refine ⟨1125850836639675451116493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1501134448852900601488657 1125850836639675451116493)
                    ·
                      refine ⟨422194063739878294168685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125850836639675451116493 422194063739878294168685)
                      ·
                        rfl

theorem cell23_822220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_822220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822220 prefixEnd_822220 := by exact prefixLift 822220
  have htrace : WordTrace (prefixWord ++ tailWord_822220) baseStart_822220 baseEnd_822220 := by
    simpa [prefixWord, tailWord_822220, baseEnd_822220] using wordTrace_append hprefix tailTrace_822220
  have hstable : (prefixWord ++ tailWord_822220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822220).length < 2 ^ (prefixWord ++ tailWord_822220).sum := by decide
  have hdescent : baseEnd_822220 < baseStart_822220 := by decide
  rcases family_descends (prefixWord ++ tailWord_822220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822223 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 8]
def baseStart_822223 : Nat := 118140960795 + 822223 * 2 ^ 59
def prefixEnd_822223 : Nat := 4983230072969 + 3 ^ 40 * 822223 * 2
def baseEnd_822223 : Nat := 46910622686871309159019

theorem tailTrace_822223 : CollatzResearch.WordTrace tailWord_822223 prefixEnd_822223 46910622686871309159019 := by
  unfold tailWord_822223
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988936500233970353743323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19992624333489313569162215 29988936500233970353743323)
  ·
    refine ⟨44983404750350955530614985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29988936500233970353743323 44983404750350955530614985)
    ·
      refine ⟨33737553562763216647961239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44983404750350955530614985 33737553562763216647961239)
      ·
        refine ⟨50606330344144824971941859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33737553562763216647961239 50606330344144824971941859)
        ·
          refine ⟨75909495516217237457912789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50606330344144824971941859 75909495516217237457912789)
          ·
            refine ⟨1779128801161341502919831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75909495516217237457912789 1779128801161341502919831)
            ·
              refine ⟨2668693201742012254379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779128801161341502919831 2668693201742012254379747)
              ·
                refine ⟨4003039802613018381569621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668693201742012254379747 4003039802613018381569621)
                ·
                  refine ⟨46910622686871309159019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4003039802613018381569621 46910622686871309159019)
                  ·
                    rfl

theorem cell23_822223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 8].length) (baseStart_822223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822223 prefixEnd_822223 := by exact prefixLift 822223
  have htrace : WordTrace (prefixWord ++ tailWord_822223) baseStart_822223 baseEnd_822223 := by
    simpa [prefixWord, tailWord_822223, baseEnd_822223] using wordTrace_append hprefix tailTrace_822223
  have hstable : (prefixWord ++ tailWord_822223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822223).length < 2 ^ (prefixWord ++ tailWord_822223).sum := by decide
  have hdescent : baseEnd_822223 < baseStart_822223 := by decide
  rcases family_descends (prefixWord ++ tailWord_822223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822243 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_822243 : Nat := 118140960795 + 822243 * 2 ^ 59
def prefixEnd_822243 : Nat := 4983230072969 + 3 ^ 40 * 822243 * 2
def baseEnd_822243 : Nat := 422205873794931704181079

theorem tailTrace_822243 : CollatzResearch.WordTrace tailWord_822243 prefixEnd_822243 422205873794931704181079 := by
  unfold tailWord_822243
  simp only [CollatzResearch.WordTrace]
  refine ⟨29989665960161513769471383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19993110640107675846314255 29989665960161513769471383)
  ·
    refine ⟨44984498940242270654207075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29989665960161513769471383 44984498940242270654207075)
    ·
      refine ⟨67476748410363405981310613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44984498940242270654207075 67476748410363405981310613)
      ·
        refine ⟨3162972581735784655373935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67476748410363405981310613 3162972581735784655373935)
        ·
          refine ⟨4744458872603676983060903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162972581735784655373935 4744458872603676983060903)
          ·
            refine ⟨7116688308905515474591355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744458872603676983060903 7116688308905515474591355)
            ·
              refine ⟨10675032463358273211887033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116688308905515474591355 10675032463358273211887033)
              ·
                refine ⟨8006274347518704908915275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675032463358273211887033 8006274347518704908915275)
                ·
                  refine ⟨12009411521278057363372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006274347518704908915275 12009411521278057363372913)
                  ·
                    refine ⟨9007058640958543022529685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12009411521278057363372913 9007058640958543022529685)
                    ·
                      refine ⟨422205873794931704181079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9007058640958543022529685 422205873794931704181079)
                      ·
                        rfl

theorem cell23_822243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_822243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822243 prefixEnd_822243 := by exact prefixLift 822243
  have htrace : WordTrace (prefixWord ++ tailWord_822243) baseStart_822243 baseEnd_822243 := by
    simpa [prefixWord, tailWord_822243, baseEnd_822243] using wordTrace_append hprefix tailTrace_822243
  have hstable : (prefixWord ++ tailWord_822243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822243).length < 2 ^ (prefixWord ++ tailWord_822243).sum := by decide
  have hdescent : baseEnd_822243 < baseStart_822243 := by decide
  rcases family_descends (prefixWord ++ tailWord_822243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822277 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_822277 : Nat := 118140960795 + 822277 * 2 ^ 59
def prefixEnd_822277 : Nat := 4983230072969 + 3 ^ 40 * 822277 * 2
def baseEnd_822277 : Nat := 422223332137184571155923

theorem tailTrace_822277 : CollatzResearch.WordTrace tailWord_822277 prefixEnd_822277 422223332137184571155923 := by
  unfold tailWord_822277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29990906042038337576209085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19993937361358891717472723 29990906042038337576209085)
  ·
    refine ⟨11246589765764376591078407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29990906042038337576209085 11246589765764376591078407)
    ·
      refine ⟨16869884648646564886617611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246589765764376591078407 16869884648646564886617611)
      ·
        refine ⟨25304826972969847329926417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16869884648646564886617611 25304826972969847329926417)
        ·
          refine ⟨18978620229727385497444813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25304826972969847329926417 18978620229727385497444813)
          ·
            refine ⟨7116982586147769561541805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18978620229727385497444813 7116982586147769561541805)
            ·
              refine ⟨2668868469805413585578177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7116982586147769561541805 2668868469805413585578177)
              ·
                refine ⟨2001651352354060189183633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668868469805413585578177 2001651352354060189183633)
                ·
                  refine ⟨1501238514265545141887725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001651352354060189183633 1501238514265545141887725)
                  ·
                    refine ⟨562964442849579428207897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501238514265545141887725 562964442849579428207897)
                    ·
                      refine ⟨422223332137184571155923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562964442849579428207897 422223332137184571155923)
                      ·
                        rfl

theorem cell23_822277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_822277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822277 prefixEnd_822277 := by exact prefixLift 822277
  have htrace : WordTrace (prefixWord ++ tailWord_822277) baseStart_822277 baseEnd_822277 := by
    simpa [prefixWord, tailWord_822277, baseEnd_822277] using wordTrace_append hprefix tailTrace_822277
  have hstable : (prefixWord ++ tailWord_822277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822277).length < 2 ^ (prefixWord ++ tailWord_822277).sum := by decide
  have hdescent : baseEnd_822277 < baseStart_822277 := by decide
  rcases family_descends (prefixWord ++ tailWord_822277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822284 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_822284 : Nat := 118140960795 + 822284 * 2 ^ 59
def prefixEnd_822284 : Nat := 4983230072969 + 3 ^ 40 * 822284 * 2
def baseEnd_822284 : Nat := 422226926501766043768391

theorem tailTrace_822284 : CollatzResearch.WordTrace tailWord_822284 prefixEnd_822284 422226926501766043768391 := by
  unfold tailWord_822284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14995580676506488885856953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19994107568675318514475937 14995580676506488885856953)
  ·
    refine ⟨11246685507379866664392715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14995580676506488885856953 11246685507379866664392715)
    ·
      refine ⟨16870028261069799996589073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246685507379866664392715 16870028261069799996589073)
      ·
        refine ⟨12652521195802349997441805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16870028261069799996589073 12652521195802349997441805)
        ·
          refine ⟨4744695448425881249040677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12652521195802349997441805 4744695448425881249040677)
          ·
            refine ⟨889630396579852734195127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4744695448425881249040677 889630396579852734195127)
            ·
              refine ⟨1334445594869779101292691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889630396579852734195127 1334445594869779101292691)
              ·
                refine ⟨2001668392304668651939037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334445594869779101292691 2001668392304668651939037)
                ·
                  refine ⟨750625647114250744477139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2001668392304668651939037 750625647114250744477139)
                  ·
                    refine ⟨1125938470671376116715709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750625647114250744477139 1125938470671376116715709)
                    ·
                      refine ⟨422226926501766043768391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1125938470671376116715709 422226926501766043768391)
                      ·
                        rfl

theorem cell23_822284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_822284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822284 prefixEnd_822284 := by exact prefixLift 822284
  have htrace : WordTrace (prefixWord ++ tailWord_822284) baseStart_822284 baseEnd_822284 := by
    simpa [prefixWord, tailWord_822284, baseEnd_822284] using wordTrace_append hprefix tailTrace_822284
  have hstable : (prefixWord ++ tailWord_822284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822284).length < 2 ^ (prefixWord ++ tailWord_822284).sum := by decide
  have hdescent : baseEnd_822284 < baseStart_822284 := by decide
  rcases family_descends (prefixWord ++ tailWord_822284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822307 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 4]
def baseStart_822307 : Nat := 118140960795 + 822307 * 2 ^ 59
def prefixEnd_822307 : Nat := 4983230072969 + 3 ^ 40 * 822307 * 2
def baseEnd_822307 : Nat := 422238736556819453780785

theorem tailTrace_822307 : CollatzResearch.WordTrace tailWord_822307 prefixEnd_822307 422238736556819453780785 := by
  unfold tailWord_822307
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992000231929652699801175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19994666821286435133200783 29992000231929652699801175)
  ·
    refine ⟨44988000347894479049701763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992000231929652699801175 44988000347894479049701763)
    ·
      refine ⟨67482000521841718574552645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44988000347894479049701763 67482000521841718574552645)
      ·
        refine ⟨12652875097845322232728621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67482000521841718574552645 12652875097845322232728621)
        ·
          refine ⟨4744828161691995837273233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12652875097845322232728621 4744828161691995837273233)
          ·
            refine ⟨3558621121268996877954925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744828161691995837273233 3558621121268996877954925)
            ·
              refine ⟨1334482920475873829233097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558621121268996877954925 1334482920475873829233097)
              ·
                refine ⟨1000862190356905371924823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334482920475873829233097 1000862190356905371924823)
                ·
                  refine ⟨1501293285535358057887235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000862190356905371924823 1501293285535358057887235)
                  ·
                    refine ⟨2251939928303037086830853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501293285535358057887235 2251939928303037086830853)
                    ·
                      refine ⟨422238736556819453780785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2251939928303037086830853 422238736556819453780785)
                      ·
                        rfl

theorem cell23_822307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_822307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822307 prefixEnd_822307 := by exact prefixLift 822307
  have htrace : WordTrace (prefixWord ++ tailWord_822307) baseStart_822307 baseEnd_822307 := by
    simpa [prefixWord, tailWord_822307, baseEnd_822307] using wordTrace_append hprefix tailTrace_822307
  have hstable : (prefixWord ++ tailWord_822307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822307).length < 2 ^ (prefixWord ++ tailWord_822307).sum := by decide
  have hdescent : baseEnd_822307 < baseStart_822307 := by decide
  rcases family_descends (prefixWord ++ tailWord_822307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822311 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_822311 : Nat := 118140960795 + 822311 * 2 ^ 59
def prefixEnd_822311 : Nat := 4983230072969 + 3 ^ 40 * 822311 * 2
def baseEnd_822311 : Nat := 422240790479437438130767

theorem tailTrace_822311 : CollatzResearch.WordTrace tailWord_822311 prefixEnd_822311 422240790479437438130767 := by
  unfold tailWord_822311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992146123915161382946787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19994764082610107588631191 29992146123915161382946787)
  ·
    refine ⟨44988219185872742074420181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992146123915161382946787 44988219185872742074420181)
    ·
      refine ⟨1054411387168892392369223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44988219185872742074420181 1054411387168892392369223)
      ·
        refine ⟨1581617080753338588553835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054411387168892392369223 1581617080753338588553835)
        ·
          refine ⟨2372425621130007882830753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581617080753338588553835 2372425621130007882830753)
          ·
            refine ⟨1779319215847505912123065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372425621130007882830753 1779319215847505912123065)
            ·
              refine ⟨1334489411885629434092299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779319215847505912123065 1334489411885629434092299)
              ·
                refine ⟨2001734117828444151138449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334489411885629434092299 2001734117828444151138449)
                ·
                  refine ⟨1501300588371333113353837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001734117828444151138449 1501300588371333113353837)
                  ·
                    refine ⟨562987720639249917507689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501300588371333113353837 562987720639249917507689)
                    ·
                      refine ⟨422240790479437438130767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 562987720639249917507689 422240790479437438130767)
                      ·
                        rfl

theorem cell23_822311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_822311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822311 prefixEnd_822311 := by exact prefixLift 822311
  have htrace : WordTrace (prefixWord ++ tailWord_822311) baseStart_822311 baseEnd_822311 := by
    simpa [prefixWord, tailWord_822311, baseEnd_822311] using wordTrace_append hprefix tailTrace_822311
  have hstable : (prefixWord ++ tailWord_822311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822311).length < 2 ^ (prefixWord ++ tailWord_822311).sum := by decide
  have hdescent : baseEnd_822311 < baseStart_822311 := by decide
  rcases family_descends (prefixWord ++ tailWord_822311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822320 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_822320 : Nat := 118140960795 + 822320 * 2 ^ 59
def prefixEnd_822320 : Nat := 4983230072969 + 3 ^ 40 * 822320 * 2
def baseEnd_822320 : Nat := 422245411805327902918225

theorem tailTrace_822320 : CollatzResearch.WordTrace tailWord_822320 prefixEnd_822320 422245411805327902918225 := by
  unfold tailWord_822320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996237190441277960012207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19994982920588370613349609 14996237190441277960012207)
  ·
    refine ⟨22494355785661916940018311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14996237190441277960012207 22494355785661916940018311)
    ·
      refine ⟨33741533678492875410027467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22494355785661916940018311 33741533678492875410027467)
      ·
        refine ⟨50612300517739313115041201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33741533678492875410027467 50612300517739313115041201)
        ·
          refine ⟨37959225388304484836280901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50612300517739313115041201 37959225388304484836280901)
          ·
            refine ⟨7117354760307090906802669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37959225388304484836280901 7117354760307090906802669)
            ·
              refine ⟨2669008035115159090051001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7117354760307090906802669 2669008035115159090051001)
              ·
                refine ⟨2001756026336369317538251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669008035115159090051001 2001756026336369317538251)
                ·
                  refine ⟨3002634039504553976307377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001756026336369317538251 3002634039504553976307377)
                  ·
                    refine ⟨2251975529628415482230533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3002634039504553976307377 2251975529628415482230533)
                    ·
                      refine ⟨422245411805327902918225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2251975529628415482230533 422245411805327902918225)
                      ·
                        rfl

theorem cell23_822320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_822320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822320 prefixEnd_822320 := by exact prefixLift 822320
  have htrace : WordTrace (prefixWord ++ tailWord_822320) baseStart_822320 baseEnd_822320 := by
    simpa [prefixWord, tailWord_822320, baseEnd_822320] using wordTrace_append hprefix tailTrace_822320
  have hstable : (prefixWord ++ tailWord_822320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822320).length < 2 ^ (prefixWord ++ tailWord_822320).sum := by decide
  have hdescent : baseEnd_822320 < baseStart_822320 := by decide
  rcases family_descends (prefixWord ++ tailWord_822320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822334 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_822334 : Nat := 118140960795 + 822334 * 2 ^ 59
def prefixEnd_822334 : Nat := 4983230072969 + 3 ^ 40 * 822334 * 2
def baseEnd_822334 : Nat := 140750866844830282714387

theorem tailTrace_822334 : CollatzResearch.WordTrace tailWord_822334 prefixEnd_822334 140750866844830282714387 := by
  unfold tailWord_822334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749123125353979538879257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19995323335221224207356037 3749123125353979538879257)
  ·
    refine ⟨2811842344015484654159443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3749123125353979538879257 2811842344015484654159443)
    ·
      refine ⟨4217763516023226981239165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811842344015484654159443 4217763516023226981239165)
      ·
        refine ⟨1581661318508710117964687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4217763516023226981239165 1581661318508710117964687)
        ·
          refine ⟨2372491977763065176947031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581661318508710117964687 2372491977763065176947031)
          ·
            refine ⟨3558737966644597765420547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372491977763065176947031 3558737966644597765420547)
            ·
              refine ⟨5338106949966896648130821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558737966644597765420547 5338106949966896648130821)
              ·
                refine ⟨1000895053118793121524529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5338106949966896648130821 1000895053118793121524529)
                ·
                  refine ⟨750671289839094841143397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000895053118793121524529 750671289839094841143397)
                  ·
                    refine ⟨140750866844830282714387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750671289839094841143397 140750866844830282714387)
                    ·
                      rfl

theorem cell23_822334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_822334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822334 prefixEnd_822334 := by exact prefixLift 822334
  have htrace : WordTrace (prefixWord ++ tailWord_822334) baseStart_822334 baseEnd_822334 := by
    simpa [prefixWord, tailWord_822334, baseEnd_822334] using wordTrace_append hprefix tailTrace_822334
  have hstable : (prefixWord ++ tailWord_822334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822334).length < 2 ^ (prefixWord ++ tailWord_822334).sum := by decide
  have hdescent : baseEnd_822334 < baseStart_822334 := by decide
  rcases family_descends (prefixWord ++ tailWord_822334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822357 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_822357 : Nat := 118140960795 + 822357 * 2 ^ 59
def prefixEnd_822357 : Nat := 4983230072969 + 3 ^ 40 * 822357 * 2
def baseEnd_822357 : Nat := 422264410589544258155555

theorem tailTrace_822357 : CollatzResearch.WordTrace tailWord_822357 prefixEnd_822357 422264410589544258155555 := by
  unfold tailWord_822357
  simp only [CollatzResearch.WordTrace]
  refine ⟨29993823881748511239121325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19995882587832340826080883 29993823881748511239121325)
  ·
    refine ⟨11247683955655691714670497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29993823881748511239121325 11247683955655691714670497)
    ·
      refine ⟨8435762966741768786002873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11247683955655691714670497 8435762966741768786002873)
      ·
        refine ⟨6326822225056326589502155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435762966741768786002873 6326822225056326589502155)
        ·
          refine ⟨9490233337584489884253233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6326822225056326589502155 9490233337584489884253233)
          ·
            refine ⟨7117675003188367413189925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9490233337584489884253233 7117675003188367413189925)
            ·
              refine ⟨1334564063097818889973111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7117675003188367413189925 1334564063097818889973111)
              ·
                refine ⟨2001846094646728334959667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334564063097818889973111 2001846094646728334959667)
                ·
                  refine ⟨3002769141970092502439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001846094646728334959667 3002769141970092502439501)
                  ·
                    refine ⟨1126038428238784688414813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002769141970092502439501 1126038428238784688414813)
                    ·
                      refine ⟨422264410589544258155555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126038428238784688414813 422264410589544258155555)
                      ·
                        rfl

theorem cell23_822357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_822357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822357 prefixEnd_822357 := by exact prefixLift 822357
  have htrace : WordTrace (prefixWord ++ tailWord_822357) baseStart_822357 baseEnd_822357 := by
    simpa [prefixWord, tailWord_822357, baseEnd_822357] using wordTrace_append hprefix tailTrace_822357
  have hstable : (prefixWord ++ tailWord_822357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822357).length < 2 ^ (prefixWord ++ tailWord_822357).sum := by decide
  have hdescent : baseEnd_822357 < baseStart_822357 := by decide
  rcases family_descends (prefixWord ++ tailWord_822357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822367 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 3, 3, 2]
def baseStart_822367 : Nat := 118140960795 + 822367 * 2 ^ 59
def prefixEnd_822367 : Nat := 4983230072969 + 3 ^ 40 * 822367 * 2
def baseEnd_822367 : Nat := 422269545396089219030509

theorem tailTrace_822367 : CollatzResearch.WordTrace tailWord_822367 prefixEnd_822367 422269545396089219030509 := by
  unfold tailWord_822367
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994188611712282946985355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19996125741141521964656903 29994188611712282946985355)
  ·
    refine ⟨44991282917568424420478033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29994188611712282946985355 44991282917568424420478033)
    ·
      refine ⟨33743462188176318315358525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44991282917568424420478033 33743462188176318315358525)
      ·
        refine ⟨12653798320566119368259447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33743462188176318315358525 12653798320566119368259447)
        ·
          refine ⟨18980697480849179052389171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653798320566119368259447 18980697480849179052389171)
          ·
            refine ⟨28471046221273768578583757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980697480849179052389171 28471046221273768578583757)
            ·
              refine ⟨10676642332977663216968909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28471046221273768578583757 10676642332977663216968909)
              ·
                refine ⟨4003740874866623706363341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676642332977663216968909 4003740874866623706363341)
                ·
                  refine ⟨1501402828074983889886253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4003740874866623706363341 1501402828074983889886253)
                  ·
                    refine ⟨563026060528118958707345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501402828074983889886253 563026060528118958707345)
                    ·
                      refine ⟨422269545396089219030509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563026060528118958707345 422269545396089219030509)
                      ·
                        rfl

theorem cell23_822367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_822367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822367 prefixEnd_822367 := by exact prefixLift 822367
  have htrace : WordTrace (prefixWord ++ tailWord_822367) baseStart_822367 baseEnd_822367 := by
    simpa [prefixWord, tailWord_822367, baseEnd_822367] using wordTrace_append hprefix tailTrace_822367
  have hstable : (prefixWord ++ tailWord_822367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822367).length < 2 ^ (prefixWord ++ tailWord_822367).sum := by decide
  have hdescent : baseEnd_822367 < baseStart_822367 := by decide
  rcases family_descends (prefixWord ++ tailWord_822367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822384 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2]
def baseStart_822384 : Nat := 118140960795 + 822384 * 2 ^ 59
def prefixEnd_822384 : Nat := 4983230072969 + 3 ^ 40 * 822384 * 2
def baseEnd_822384 : Nat := 422278274567215652517931

theorem tailTrace_822384 : CollatzResearch.WordTrace tailWord_822384 prefixEnd_822384 422278274567215652517931 := by
  unfold tailWord_822384
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997404326325347425177103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19996539101767129900236137 14997404326325347425177103)
  ·
    refine ⟨22496106489488021137765655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997404326325347425177103 22496106489488021137765655)
    ·
      refine ⟨33744159734232031706648483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496106489488021137765655 33744159734232031706648483)
      ·
        refine ⟨50616239601348047559972725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33744159734232031706648483 50616239601348047559972725)
        ·
          refine ⟨4745272462626379458747443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50616239601348047559972725 4745272462626379458747443)
          ·
            refine ⟨7117908693939569188121165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745272462626379458747443 7117908693939569188121165)
            ·
              refine ⟨2669215760227338445545437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7117908693939569188121165 2669215760227338445545437)
              ·
                refine ⟨1000955910085251917079539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2669215760227338445545437 1000955910085251917079539)
                ·
                  refine ⟨1501433865127877875619309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000955910085251917079539 1501433865127877875619309)
                  ·
                    refine ⟨563037699422954203357241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501433865127877875619309 563037699422954203357241)
                    ·
                      refine ⟨422278274567215652517931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563037699422954203357241 422278274567215652517931)
                      ·
                        rfl

theorem cell23_822384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2].length) (baseStart_822384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822384 prefixEnd_822384 := by exact prefixLift 822384
  have htrace : WordTrace (prefixWord ++ tailWord_822384) baseStart_822384 baseEnd_822384 := by
    simpa [prefixWord, tailWord_822384, baseEnd_822384] using wordTrace_append hprefix tailTrace_822384
  have hstable : (prefixWord ++ tailWord_822384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822384).length < 2 ^ (prefixWord ++ tailWord_822384).sum := by decide
  have hdescent : baseEnd_822384 < baseStart_822384 := by decide
  rcases family_descends (prefixWord ++ tailWord_822384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822400 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_822400 : Nat := 118140960795 + 822400 * 2 ^ 59
def prefixEnd_822400 : Nat := 4983230072969 + 3 ^ 40 * 822400 * 2
def baseEnd_822400 : Nat := 422286490257687589917857

theorem tailTrace_822400 : CollatzResearch.WordTrace tailWord_822400 prefixEnd_822400 422286490257687589917857 := by
  unfold tailWord_822400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997696110296364791468327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19996928147061819721957769 14997696110296364791468327)
  ·
    refine ⟨22496544165444547187202491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997696110296364791468327 22496544165444547187202491)
    ·
      refine ⟨33744816248166820780803737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496544165444547187202491 33744816248166820780803737)
      ·
        refine ⟨25308612186125115585602803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33744816248166820780803737 25308612186125115585602803)
        ·
          refine ⟨37962918279187673378404205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25308612186125115585602803 37962918279187673378404205)
          ·
            refine ⟨14236094354695377516901577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37962918279187673378404205 14236094354695377516901577)
            ·
              refine ⟨10677070766021533137676183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14236094354695377516901577 10677070766021533137676183)
              ·
                refine ⟨16015606149032299706514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10677070766021533137676183 16015606149032299706514275)
                ·
                  refine ⟨24023409223548449559771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015606149032299706514275 24023409223548449559771413)
                  ·
                    refine ⟨1126097307353833573114285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24023409223548449559771413 1126097307353833573114285)
                    ·
                      refine ⟨422286490257687589917857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126097307353833573114285 422286490257687589917857)
                      ·
                        rfl

theorem cell23_822400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_822400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822400 prefixEnd_822400 := by exact prefixLift 822400
  have htrace : WordTrace (prefixWord ++ tailWord_822400) baseStart_822400 baseEnd_822400 := by
    simpa [prefixWord, tailWord_822400, baseEnd_822400] using wordTrace_append hprefix tailTrace_822400
  have hstable : (prefixWord ++ tailWord_822400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822400).length < 2 ^ (prefixWord ++ tailWord_822400).sum := by decide
  have hdescent : baseEnd_822400 < baseStart_822400 := by decide
  rcases family_descends (prefixWord ++ tailWord_822400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822408 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_822408 : Nat := 118140960795 + 822408 * 2 ^ 59
def prefixEnd_822408 : Nat := 4983230072969 + 3 ^ 40 * 822408 * 2
def baseEnd_822408 : Nat := 422290598102923558617821

theorem tailTrace_822408 : CollatzResearch.WordTrace tailWord_822408 prefixEnd_822408 422290598102923558617821 := by
  unfold tailWord_822408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997842002281873474613939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19997122669709164632818585 14997842002281873474613939)
  ·
    refine ⟨22496763003422810211920909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997842002281873474613939 22496763003422810211920909)
    ·
      refine ⟨8436286126283553829470341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22496763003422810211920909 8436286126283553829470341)
      ·
        refine ⟨1581803648678166343025689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8436286126283553829470341 1581803648678166343025689)
        ·
          refine ⟨1186352736508624757269267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581803648678166343025689 1186352736508624757269267)
          ·
            refine ⟨1779529104762937135903901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186352736508624757269267 1779529104762937135903901)
            ·
              refine ⟨667323414286101425963963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1779529104762937135903901 667323414286101425963963)
              ·
                refine ⟨1000985121429152138945945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667323414286101425963963 1000985121429152138945945)
                ·
                  refine ⟨750738841071864104209459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000985121429152138945945 750738841071864104209459)
                  ·
                    refine ⟨1126108261607796156314189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750738841071864104209459 1126108261607796156314189)
                    ·
                      refine ⟨422290598102923558617821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126108261607796156314189 422290598102923558617821)
                      ·
                        rfl

theorem cell23_822408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_822408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822408 prefixEnd_822408 := by exact prefixLift 822408
  have htrace : WordTrace (prefixWord ++ tailWord_822408) baseStart_822408 baseEnd_822408 := by
    simpa [prefixWord, tailWord_822408, baseEnd_822408] using wordTrace_append hprefix tailTrace_822408
  have hstable : (prefixWord ++ tailWord_822408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822408).length < 2 ^ (prefixWord ++ tailWord_822408).sum := by decide
  have hdescent : baseEnd_822408 < baseStart_822408 := by decide
  rcases family_descends (prefixWord ++ tailWord_822408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822434 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_822434 : Nat := 118140960795 + 822434 * 2 ^ 59
def prefixEnd_822434 : Nat := 4983230072969 + 3 ^ 40 * 822434 * 2
def baseEnd_822434 : Nat := 422303948599940456892701

theorem tailTrace_822434 : CollatzResearch.WordTrace tailWord_822434 prefixEnd_822434 422303948599940456892701 := by
  unfold tailWord_822434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499158075617388347418589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19997754868313035593116237 7499158075617388347418589)
  ·
    refine ⟨2812184278356520630281971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7499158075617388347418589 2812184278356520630281971)
    ·
      refine ⟨4218276417534780945422957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812184278356520630281971 4218276417534780945422957)
      ·
        refine ⟨1581853656575542854533609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4218276417534780945422957 1581853656575542854533609)
        ·
          refine ⟨1186390242431657140900207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581853656575542854533609 1186390242431657140900207)
          ·
            refine ⟨1779585363647485711350311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186390242431657140900207 1779585363647485711350311)
            ·
              refine ⟨2669378045471228567025467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779585363647485711350311 2669378045471228567025467)
              ·
                refine ⟨4004067068206842850538201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669378045471228567025467 4004067068206842850538201)
                ·
                  refine ⟨3003050301155132137903651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004067068206842850538201 3003050301155132137903651)
                  ·
                    refine ⟨4504575451732698206855477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3003050301155132137903651 4504575451732698206855477)
                    ·
                      refine ⟨422303948599940456892701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4504575451732698206855477 422303948599940456892701)
                      ·
                        rfl

theorem cell23_822434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_822434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822434 prefixEnd_822434 := by exact prefixLift 822434
  have htrace : WordTrace (prefixWord ++ tailWord_822434) baseStart_822434 baseEnd_822434 := by
    simpa [prefixWord, tailWord_822434, baseEnd_822434] using wordTrace_append hprefix tailTrace_822434
  have hstable : (prefixWord ++ tailWord_822434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822434).length < 2 ^ (prefixWord ++ tailWord_822434).sum := by decide
  have hdescent : baseEnd_822434 < baseStart_822434 := by decide
  rcases family_descends (prefixWord ++ tailWord_822434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822465 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_822465 : Nat := 118140960795 + 822465 * 2 ^ 59
def prefixEnd_822465 : Nat := 4983230072969 + 3 ^ 40 * 822465 * 2
def baseEnd_822465 : Nat := 422319866500229835605059

theorem tailTrace_822465 : CollatzResearch.WordTrace tailWord_822465 prefixEnd_822465 422319866500229835605059 := by
  unfold tailWord_822465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997762965357245684052849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19998508643571497122701899 29997762965357245684052849)
  ·
    refine ⟨22498322224017934263039637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29997762965357245684052849 22498322224017934263039637)
    ·
      refine ⟨1054608854250840668579983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22498322224017934263039637 1054608854250840668579983)
      ·
        refine ⟨1581913281376261002869975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054608854250840668579983 1581913281376261002869975)
        ·
          refine ⟨2372869922064391504304963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581913281376261002869975 2372869922064391504304963)
          ·
            refine ⟨3559304883096587256457445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372869922064391504304963 3559304883096587256457445)
            ·
              refine ⟨667369665580610110585771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3559304883096587256457445 667369665580610110585771)
              ·
                refine ⟨1001054498370915165878657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667369665580610110585771 1001054498370915165878657)
                ·
                  refine ⟨750790873778186374408993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1001054498370915165878657 750790873778186374408993)
                  ·
                    refine ⟨563093155333639780806745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750790873778186374408993 563093155333639780806745)
                    ·
                      refine ⟨422319866500229835605059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563093155333639780806745 422319866500229835605059)
                      ·
                        rfl

theorem cell23_822465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_822465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822465 prefixEnd_822465 := by exact prefixLift 822465
  have htrace : WordTrace (prefixWord ++ tailWord_822465) baseStart_822465 baseEnd_822465 := by
    simpa [prefixWord, tailWord_822465, baseEnd_822465] using wordTrace_append hprefix tailTrace_822465
  have hstable : (prefixWord ++ tailWord_822465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822465).length < 2 ^ (prefixWord ++ tailWord_822465).sum := by decide
  have hdescent : baseEnd_822465 < baseStart_822465 := by decide
  rcases family_descends (prefixWord ++ tailWord_822465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822487 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_822487 : Nat := 118140960795 + 822487 * 2 ^ 59
def prefixEnd_822487 : Nat := 4983230072969 + 3 ^ 40 * 822487 * 2
def baseEnd_822487 : Nat := 422331163074628749529957

theorem tailTrace_822487 : CollatzResearch.WordTrace tailWord_822487 prefixEnd_822487 422331163074628749529957 := by
  unfold tailWord_822487
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998565371277543441353715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19999043580851695627569143 29998565371277543441353715)
  ·
    refine ⟨44997848056916315162030573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29998565371277543441353715 44997848056916315162030573)
    ·
      refine ⟨16874193021343618185761465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44997848056916315162030573 16874193021343618185761465)
      ·
        refine ⟨12655644766007713639321099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16874193021343618185761465 12655644766007713639321099)
        ·
          refine ⟨18983467149011570458981649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12655644766007713639321099 18983467149011570458981649)
          ·
            refine ⟨14237600361758677844236237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18983467149011570458981649 14237600361758677844236237)
            ·
              refine ⟨5339100135659504191588589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14237600361758677844236237 5339100135659504191588589)
              ·
                refine ⟨2002162550872314071845721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5339100135659504191588589 2002162550872314071845721)
                ·
                  refine ⟨1501621913154235553884291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002162550872314071845721 1501621913154235553884291)
                  ·
                    refine ⟨2252432869731353330826437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501621913154235553884291 2252432869731353330826437)
                    ·
                      refine ⟨422331163074628749529957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2252432869731353330826437 422331163074628749529957)
                      ·
                        rfl

theorem cell23_822487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_822487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822487 prefixEnd_822487 := by exact prefixLift 822487
  have htrace : WordTrace (prefixWord ++ tailWord_822487) baseStart_822487 baseEnd_822487 := by
    simpa [prefixWord, tailWord_822487, baseEnd_822487] using wordTrace_append hprefix tailTrace_822487
  have hstable : (prefixWord ++ tailWord_822487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822487).length < 2 ^ (prefixWord ++ tailWord_822487).sum := by decide
  have hdescent : baseEnd_822487 < baseStart_822487 := by decide
  rcases family_descends (prefixWord ++ tailWord_822487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822504 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_822504 : Nat := 118140960795 + 822504 * 2 ^ 59
def prefixEnd_822504 : Nat := 4983230072969 + 3 ^ 40 * 822504 * 2
def baseEnd_822504 : Nat := 422339892245755183017379

theorem tailTrace_822504 : CollatzResearch.WordTrace tailWord_822504 prefixEnd_822504 422339892245755183017379 := by
  unfold tailWord_822504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14999592706107977672361283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19999456941477303563148377 14999592706107977672361283)
  ·
    refine ⟨22499389059161966508541925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14999592706107977672361283 22499389059161966508541925)
    ·
      refine ⟨4218635448592868720351611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22499389059161966508541925 4218635448592868720351611)
      ·
        refine ⟨6327953172889303080527417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218635448592868720351611 6327953172889303080527417)
        ·
          refine ⟨4745964879666977310395563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6327953172889303080527417 4745964879666977310395563)
          ·
            refine ⟨7118947319500465965593345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745964879666977310395563 7118947319500465965593345)
            ·
              refine ⟨5339210489625349474195009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118947319500465965593345 5339210489625349474195009)
              ·
                refine ⟨4004407867219012105646257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339210489625349474195009 4004407867219012105646257)
                ·
                  refine ⟨3003305900414259079234693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004407867219012105646257 3003305900414259079234693)
                  ·
                    refine ⟨563119856327673577356505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3003305900414259079234693 563119856327673577356505)
                    ·
                      refine ⟨422339892245755183017379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563119856327673577356505 422339892245755183017379)
                      ·
                        rfl

theorem cell23_822504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_822504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822504 prefixEnd_822504 := by exact prefixLift 822504
  have htrace : WordTrace (prefixWord ++ tailWord_822504) baseStart_822504 baseEnd_822504 := by
    simpa [prefixWord, tailWord_822504, baseEnd_822504] using wordTrace_append hprefix tailTrace_822504
  have hstable : (prefixWord ++ tailWord_822504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822504).length < 2 ^ (prefixWord ++ tailWord_822504).sum := by decide
  have hdescent : baseEnd_822504 < baseStart_822504 := by decide
  rcases family_descends (prefixWord ++ tailWord_822504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822527 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 6]
def baseStart_822527 : Nat := 118140960795 + 822527 * 2 ^ 59
def prefixEnd_822527 : Nat := 4983230072969 + 3 ^ 40 * 822527 * 2
def baseEnd_822527 : Nat := 46927966922312065892197

theorem tailTrace_822527 : CollatzResearch.WordTrace tailWord_822527 prefixEnd_822527 46927966922312065892197 := by
  unfold tailWord_822527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30000024291132630272809835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20000016194088420181873223 30000024291132630272809835)
  ·
    refine ⟨45000036436698945409214753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30000024291132630272809835 45000036436698945409214753)
    ·
      refine ⟨33750027327524209056911065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45000036436698945409214753 33750027327524209056911065)
      ·
        refine ⟨25312520495643156792683299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33750027327524209056911065 25312520495643156792683299)
        ·
          refine ⟨37968780743464735189024949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25312520495643156792683299 37968780743464735189024949)
          ·
            refine ⟨3559573194699818923971089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37968780743464735189024949 3559573194699818923971089)
            ·
              refine ⟨2669679896024864192978317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559573194699818923971089 2669679896024864192978317)
              ·
                refine ⟨1001129961009324072366869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2669679896024864192978317 1001129961009324072366869)
                ·
                  refine ⟨46927966922312065892197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1001129961009324072366869 46927966922312065892197)
                  ·
                    rfl

theorem cell23_822527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 6].length) (baseStart_822527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822527 prefixEnd_822527 := by exact prefixLift 822527
  have htrace : WordTrace (prefixWord ++ tailWord_822527) baseStart_822527 baseEnd_822527 := by
    simpa [prefixWord, tailWord_822527, baseEnd_822527] using wordTrace_append hprefix tailTrace_822527
  have hstable : (prefixWord ++ tailWord_822527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822527).length < 2 ^ (prefixWord ++ tailWord_822527).sum := by decide
  have hdescent : baseEnd_822527 < baseStart_822527 := by decide
  rcases family_descends (prefixWord ++ tailWord_822527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822597 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_822597 : Nat := 118140960795 + 822597 * 2 ^ 59
def prefixEnd_822597 : Nat := 4983230072969 + 3 ^ 40 * 822597 * 2
def baseEnd_822597 : Nat := 422387645946623319154451

theorem tailTrace_822597 : CollatzResearch.WordTrace tailWord_822597 prefixEnd_822597 422387645946623319154451 := by
  unfold tailWord_822597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002577400879032227858045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20001718267252688151905363 30002577400879032227858045)
  ·
    refine ⟨11250966525329637085446767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30002577400879032227858045 11250966525329637085446767)
    ·
      refine ⟨16876449787994455628170151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250966525329637085446767 16876449787994455628170151)
      ·
        refine ⟨25314674681991683442255227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876449787994455628170151 25314674681991683442255227)
        ·
          refine ⟨37972012022987525163382841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25314674681991683442255227 37972012022987525163382841)
          ·
            refine ⟨28479009017240643872537131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37972012022987525163382841 28479009017240643872537131)
            ·
              refine ⟨42718513525860965808805697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28479009017240643872537131 42718513525860965808805697)
              ·
                refine ⟨32038885144395724356604273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42718513525860965808805697 32038885144395724356604273)
                ·
                  refine ⟨24029163858296793267453205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32038885144395724356604273 24029163858296793267453205)
                  ·
                    refine ⟨1126367055857662184411869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24029163858296793267453205 1126367055857662184411869)
                    ·
                      refine ⟨422387645946623319154451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126367055857662184411869 422387645946623319154451)
                      ·
                        rfl

theorem cell23_822597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_822597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822597 prefixEnd_822597 := by exact prefixLift 822597
  have htrace : WordTrace (prefixWord ++ tailWord_822597) baseStart_822597 baseEnd_822597 := by
    simpa [prefixWord, tailWord_822597, baseEnd_822597] using wordTrace_append hprefix tailTrace_822597
  have hstable : (prefixWord ++ tailWord_822597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822597).length < 2 ^ (prefixWord ++ tailWord_822597).sum := by decide
  have hdescent : baseEnd_822597 < baseStart_822597 := by decide
  rcases family_descends (prefixWord ++ tailWord_822597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822604 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_822604 : Nat := 118140960795 + 822604 * 2 ^ 59
def prefixEnd_822604 : Nat := 4983230072969 + 3 ^ 40 * 822604 * 2
def baseEnd_822604 : Nat := 140797080103734930588973

theorem tailTrace_822604 : CollatzResearch.WordTrace tailWord_822604 prefixEnd_822604 140797080103734930588973 := by
  unfold tailWord_822604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001416355926836211681433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20001888474569114948908577 15001416355926836211681433)
  ·
    refine ⟨11251062266945127158761075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15001416355926836211681433 11251062266945127158761075)
    ·
      refine ⟨16876593400417690738141613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251062266945127158761075 16876593400417690738141613)
      ·
        refine ⟨6328722525156634026803105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16876593400417690738141613 6328722525156634026803105)
        ·
          refine ⟨4746541893867475520102329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328722525156634026803105 4746541893867475520102329)
          ·
            refine ⟨3559906420400606640076747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746541893867475520102329 3559906420400606640076747)
            ·
              refine ⟨5339859630600909960115121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559906420400606640076747 5339859630600909960115121)
              ·
                refine ⟨4004894722950682470086341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339859630600909960115121 4004894722950682470086341)
                ·
                  refine ⟨750917760553252963141189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4004894722950682470086341 750917760553252963141189)
                  ·
                    refine ⟨140797080103734930588973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750917760553252963141189 140797080103734930588973)
                    ·
                      rfl

theorem cell23_822604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_822604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822604 prefixEnd_822604 := by exact prefixLift 822604
  have htrace : WordTrace (prefixWord ++ tailWord_822604) baseStart_822604 baseEnd_822604 := by
    simpa [prefixWord, tailWord_822604, baseEnd_822604] using wordTrace_append hprefix tailTrace_822604
  have hstable : (prefixWord ++ tailWord_822604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822604).length < 2 ^ (prefixWord ++ tailWord_822604).sum := by decide
  have hdescent : baseEnd_822604 < baseStart_822604 := by decide
  rcases family_descends (prefixWord ++ tailWord_822604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822628 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_822628 : Nat := 118140960795 + 822628 * 2 ^ 59
def prefixEnd_822628 : Nat := 4983230072969 + 3 ^ 40 * 822628 * 2
def baseEnd_822628 : Nat := 422403563846912697866809

theorem tailTrace_822628 : CollatzResearch.WordTrace tailWord_822628 prefixEnd_822628 422403563846912697866809 := by
  unfold tailWord_822628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001854031883362261118269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20002472042511149681491025 15001854031883362261118269)
  ·
    refine ⟨5625695261956260847919351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15001854031883362261118269 5625695261956260847919351)
    ·
      refine ⟨8438542892934391271879027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625695261956260847919351 8438542892934391271879027)
      ·
        refine ⟨12657814339401586907818541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438542892934391271879027 12657814339401586907818541)
        ·
          refine ⟨4746680377275595090431953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12657814339401586907818541 4746680377275595090431953)
          ·
            refine ⟨3560010282956696317823965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746680377275595090431953 3560010282956696317823965)
            ·
              refine ⟨1335003856108761119183987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3560010282956696317823965 1335003856108761119183987)
              ·
                refine ⟨2002505784163141678775981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335003856108761119183987 2002505784163141678775981)
                ·
                  refine ⟨750939669061178129540993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2002505784163141678775981 750939669061178129540993)
                  ·
                    refine ⟨563204751795883597155745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750939669061178129540993 563204751795883597155745)
                    ·
                      refine ⟨422403563846912697866809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563204751795883597155745 422403563846912697866809)
                      ·
                        rfl

theorem cell23_822628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_822628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822628 prefixEnd_822628 := by exact prefixLift 822628
  have htrace : WordTrace (prefixWord ++ tailWord_822628) baseStart_822628 baseEnd_822628 := by
    simpa [prefixWord, tailWord_822628, baseEnd_822628] using wordTrace_append hprefix tailTrace_822628
  have hstable : (prefixWord ++ tailWord_822628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822628).length < 2 ^ (prefixWord ++ tailWord_822628).sum := by decide
  have hdescent : baseEnd_822628 < baseStart_822628 := by decide
  rcases family_descends (prefixWord ++ tailWord_822628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822645 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_822645 : Nat := 118140960795 + 822645 * 2 ^ 59
def prefixEnd_822645 : Nat := 4983230072969 + 3 ^ 40 * 822645 * 2
def baseEnd_822645 : Nat := 422412293018039131354231

theorem tailTrace_822645 : CollatzResearch.WordTrace tailWord_822645 prefixEnd_822645 422412293018039131354231 := by
  unfold tailWord_822645
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004328104705136425605389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20002885403136757617070259 30004328104705136425605389)
  ·
    refine ⟨11251623039264426159602021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30004328104705136425605389 11251623039264426159602021)
    ·
      refine ⟨2109679319862079904925379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11251623039264426159602021 2109679319862079904925379)
      ·
        refine ⟨3164518979793119857388069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109679319862079904925379 3164518979793119857388069)
        ·
          refine ⟨593347308711209973260263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3164518979793119857388069 593347308711209973260263)
          ·
            refine ⟨890020963066814959890395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593347308711209973260263 890020963066814959890395)
            ·
              refine ⟨1335031444600222439835593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890020963066814959890395 1335031444600222439835593)
              ·
                refine ⟨1001273583450166829876695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335031444600222439835593 1001273583450166829876695)
                ·
                  refine ⟨1501910375175250244815043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001273583450166829876695 1501910375175250244815043)
                  ·
                    refine ⟨2252865562762875367222565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501910375175250244815043 2252865562762875367222565)
                    ·
                      refine ⟨422412293018039131354231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2252865562762875367222565 422412293018039131354231)
                      ·
                        rfl

theorem cell23_822645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_822645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822645 prefixEnd_822645 := by exact prefixLift 822645
  have htrace : WordTrace (prefixWord ++ tailWord_822645) baseStart_822645 baseEnd_822645 := by
    simpa [prefixWord, tailWord_822645, baseEnd_822645] using wordTrace_append hprefix tailTrace_822645
  have hstable : (prefixWord ++ tailWord_822645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822645).length < 2 ^ (prefixWord ++ tailWord_822645).sum := by decide
  have hdescent : baseEnd_822645 < baseStart_822645 := by decide
  rcases family_descends (prefixWord ++ tailWord_822645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822658 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_822658 : Nat := 118140960795 + 822658 * 2 ^ 59
def prefixEnd_822658 : Nat := 4983230072969 + 3 ^ 40 * 822658 * 2
def baseEnd_822658 : Nat := 422418968266547580491671

theorem tailTrace_822658 : CollatzResearch.WordTrace tailWord_822658 prefixEnd_822658 422418968266547580491671 := by
  unfold tailWord_822658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501200563414509911457157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20003201502438693097219085 7501200563414509911457157)
  ·
    refine ⟨1406475105640220608398217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7501200563414509911457157 1406475105640220608398217)
    ·
      refine ⟨1054856329230165456298663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1406475105640220608398217 1054856329230165456298663)
      ·
        refine ⟨1582284493845248184447995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054856329230165456298663 1582284493845248184447995)
        ·
          refine ⟨2373426740767872276671993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582284493845248184447995 2373426740767872276671993)
          ·
            refine ⟨1780070055575904207503995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373426740767872276671993 1780070055575904207503995)
            ·
              refine ⟨2670105083363856311255993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780070055575904207503995 2670105083363856311255993)
              ·
                refine ⟨2002578812522892233441995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670105083363856311255993 2002578812522892233441995)
                ·
                  refine ⟨3003868218784338350162993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002578812522892233441995 3003868218784338350162993)
                  ·
                    refine ⟨2252901164088253762622245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3003868218784338350162993 2252901164088253762622245)
                    ·
                      refine ⟨422418968266547580491671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2252901164088253762622245 422418968266547580491671)
                      ·
                        rfl

theorem cell23_822658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_822658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822658 prefixEnd_822658 := by exact prefixLift 822658
  have htrace : WordTrace (prefixWord ++ tailWord_822658) baseStart_822658 baseEnd_822658 := by
    simpa [prefixWord, tailWord_822658, baseEnd_822658] using wordTrace_append hprefix tailTrace_822658
  have hstable : (prefixWord ++ tailWord_822658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822658).length < 2 ^ (prefixWord ++ tailWord_822658).sum := by decide
  have hdescent : baseEnd_822658 < baseStart_822658 := by decide
  rcases family_descends (prefixWord ++ tailWord_822658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822718 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_822718 : Nat := 118140960795 + 822718 * 2 ^ 59
def prefixEnd_822718 : Nat := 4983230072969 + 3 ^ 40 * 822718 * 2
def baseEnd_822718 : Nat := 422449777105817345741395

theorem tailTrace_822718 : CollatzResearch.WordTrace tailWord_822718 prefixEnd_822718 422449777105817345741395 := by
  unfold tailWord_822718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750873829180083736626601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20004660422293779928675205 3750873829180083736626601)
  ·
    refine ⟨2813155371885062802469951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3750873829180083736626601 2813155371885062802469951)
    ·
      refine ⟨4219733057827594203704927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813155371885062802469951 4219733057827594203704927)
      ·
        refine ⟨6329599586741391305557391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219733057827594203704927 6329599586741391305557391)
        ·
          refine ⟨9494399380112086958336087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329599586741391305557391 9494399380112086958336087)
          ·
            refine ⟨14241599070168130437504131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494399380112086958336087 14241599070168130437504131)
            ·
              refine ⟨21362398605252195656256197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241599070168130437504131 21362398605252195656256197)
              ·
                refine ⟨4005449738484786685548037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21362398605252195656256197 4005449738484786685548037)
                ·
                  refine ⟨751021825965897503540257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4005449738484786685548037 751021825965897503540257)
                  ·
                    refine ⟨563266369474423127655193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 751021825965897503540257 563266369474423127655193)
                    ·
                      refine ⟨422449777105817345741395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563266369474423127655193 422449777105817345741395)
                      ·
                        rfl

theorem cell23_822718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_822718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822718 prefixEnd_822718 := by exact prefixLift 822718
  have htrace : WordTrace (prefixWord ++ tailWord_822718) baseStart_822718 baseEnd_822718 := by
    simpa [prefixWord, tailWord_822718, baseEnd_822718] using wordTrace_append hprefix tailTrace_822718
  have hstable : (prefixWord ++ tailWord_822718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822718).length < 2 ^ (prefixWord ++ tailWord_822718).sum := by decide
  have hdescent : baseEnd_822718 < baseStart_822718 := by decide
  rcases family_descends (prefixWord ++ tailWord_822718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822741 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 5]
def baseStart_822741 : Nat := 118140960795 + 822741 * 2 ^ 59
def prefixEnd_822741 : Nat := 4983230072969 + 3 ^ 40 * 822741 * 2
def baseEnd_822741 : Nat := 46940176351207861750421

theorem tailTrace_822741 : CollatzResearch.WordTrace tailWord_822741 prefixEnd_822741 46940176351207861750421 := by
  unfold tailWord_822741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007829512357344821100077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20005219674904896547400051 30007829512357344821100077)
  ·
    refine ⟨11252936067134004307912529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30007829512357344821100077 11252936067134004307912529)
    ·
      refine ⟨8439702050350503230934397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11252936067134004307912529 8439702050350503230934397)
      ·
        refine ⟨3164888268881438711600399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8439702050350503230934397 3164888268881438711600399)
        ·
          refine ⟨4747332403322158067400599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164888268881438711600399 4747332403322158067400599)
          ·
            refine ⟨7120998604983237101100899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747332403322158067400599 7120998604983237101100899)
            ·
              refine ⟨10681497907474855651651349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120998604983237101100899 10681497907474855651651349)
              ·
                refine ⟨500695214412883858671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10681497907474855651651349 500695214412883858671157)
                ·
                  refine ⟨46940176351207861750421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500695214412883858671157 46940176351207861750421)
                  ·
                    rfl

theorem cell23_822741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_822741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822741 prefixEnd_822741 := by exact prefixLift 822741
  have htrace : WordTrace (prefixWord ++ tailWord_822741) baseStart_822741 baseEnd_822741 := by
    simpa [prefixWord, tailWord_822741, baseEnd_822741] using wordTrace_append hprefix tailTrace_822741
  have hstable : (prefixWord ++ tailWord_822741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822741).length < 2 ^ (prefixWord ++ tailWord_822741).sum := by decide
  have hdescent : baseEnd_822741 < baseStart_822741 := by decide
  rcases family_descends (prefixWord ++ tailWord_822741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822788 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_822788 : Nat := 118140960795 + 822788 * 2 ^ 59
def prefixEnd_822788 : Nat := 4983230072969 + 3 ^ 40 * 822788 * 2
def baseEnd_822788 : Nat := 140828573583877357288691

theorem tailTrace_822788 : CollatzResearch.WordTrace tailWord_822788 prefixEnd_822788 140828573583877357288691 := by
  unfold tailWord_822788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004771871593535924030509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006362495458047898707345 15004771871593535924030509)
  ·
    refine ⟨5626789451847575971511441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15004771871593535924030509 5626789451847575971511441)
    ·
      refine ⟨4220092088885681978633581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5626789451847575971511441 4220092088885681978633581)
      ·
        refine ⟨1582534533332130741987593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4220092088885681978633581 1582534533332130741987593)
        ·
          refine ⟨1186900899999098056490695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582534533332130741987593 1186900899999098056490695)
          ·
            refine ⟨1780351349998647084736043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186900899999098056490695 1780351349998647084736043)
            ·
              refine ⟨2670527024997970627104065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780351349998647084736043 2670527024997970627104065)
              ·
                refine ⟨2002895268748477970328049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670527024997970627104065 2002895268748477970328049)
                ·
                  refine ⟨1502171451561358477746037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002895268748477970328049 1502171451561358477746037)
                  ·
                    refine ⟨140828573583877357288691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1502171451561358477746037 140828573583877357288691)
                    ·
                      rfl

theorem cell23_822788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_822788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822788 prefixEnd_822788 := by exact prefixLift 822788
  have htrace : WordTrace (prefixWord ++ tailWord_822788) baseStart_822788 baseEnd_822788 := by
    simpa [prefixWord, tailWord_822788, baseEnd_822788] using wordTrace_append hprefix tailTrace_822788
  have hstable : (prefixWord ++ tailWord_822788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822788).length < 2 ^ (prefixWord ++ tailWord_822788).sum := by decide
  have hdescent : baseEnd_822788 < baseStart_822788 := by decide
  rcases family_descends (prefixWord ++ tailWord_822788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822791 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_822791 : Nat := 118140960795 + 822791 * 2 ^ 59
def prefixEnd_822791 : Nat := 4983230072969 + 3 ^ 40 * 822791 * 2
def baseEnd_822791 : Nat := 422487261193595560128559

theorem tailTrace_822791 : CollatzResearch.WordTrace tailWord_822791 prefixEnd_822791 422487261193595560128559 := by
  unfold tailWord_822791
  simp only [CollatzResearch.WordTrace]
  refine ⟨30009653162176203360420227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20006435441450802240280151 30009653162176203360420227)
  ·
    refine ⟨45014479743264305040630341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30009653162176203360420227 45014479743264305040630341)
    ·
      refine ⟨8440214951862057195118189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45014479743264305040630341 8440214951862057195118189)
      ·
        refine ⟨3165080606948271448169321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8440214951862057195118189 3165080606948271448169321)
        ·
          refine ⟨2373810455211203586126991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3165080606948271448169321 2373810455211203586126991)
          ·
            refine ⟨3560715682816805379190487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373810455211203586126991 3560715682816805379190487)
            ·
              refine ⟨5341073524225208068785731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560715682816805379190487 5341073524225208068785731)
              ·
                refine ⟨8011610286337812103178597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341073524225208068785731 8011610286337812103178597)
                ·
                  refine ⟨1502176928688339769345987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8011610286337812103178597 1502176928688339769345987)
                  ·
                    refine ⟨2253265393032509654018981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502176928688339769345987 2253265393032509654018981)
                    ·
                      refine ⟨422487261193595560128559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2253265393032509654018981 422487261193595560128559)
                      ·
                        rfl

theorem cell23_822791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_822791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822791 prefixEnd_822791 := by exact prefixLift 822791
  have htrace : WordTrace (prefixWord ++ tailWord_822791) baseStart_822791 baseEnd_822791 := by
    simpa [prefixWord, tailWord_822791, baseEnd_822791] using wordTrace_append hprefix tailTrace_822791
  have hstable : (prefixWord ++ tailWord_822791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822791).length < 2 ^ (prefixWord ++ tailWord_822791).sum := by decide
  have hdescent : baseEnd_822791 < baseStart_822791 := by decide
  rcases family_descends (prefixWord ++ tailWord_822791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
