import V185TrunkScan22Chunk338

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3022782 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3022782 : Nat := 118140960795 + 3022782 * 2 ^ 59
def prefixEnd_3022782 : Nat := 4983230072969 + 3 ^ 40 * 3022782 * 2
def baseEnd_3022782 : Nat := 344920017724243907827441

theorem tailTrace_3022782 : CollatzResearch.WordTrace tailWord_3022782 prefixEnd_3022782 344920017724243907827441 := by
  unfold tailWord_3022782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781239616873067363742825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73499944623323025939961733 13781239616873067363742825)
  ·
    refine ⟨10335929712654800522807119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13781239616873067363742825 10335929712654800522807119)
    ·
      refine ⟨15503894568982200784210679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10335929712654800522807119 15503894568982200784210679)
      ·
        refine ⟨23255841853473301176316019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15503894568982200784210679 23255841853473301176316019)
        ·
          refine ⟨34883762780209951764474029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23255841853473301176316019 34883762780209951764474029)
          ·
            refine ⟨13081411042578731911677761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34883762780209951764474029 13081411042578731911677761)
            ·
              refine ⟨9811058281934048933758321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13081411042578731911677761 9811058281934048933758321)
              ·
                refine ⟨7358293711450536700318741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9811058281934048933758321 7358293711450536700318741)
                ·
                  refine ⟨344920017724243907827441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7358293711450536700318741 344920017724243907827441)
                  ·
                    rfl

theorem cell22_3022782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3022782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022782 prefixEnd_3022782 := by exact prefixLift 3022782
  have htrace : WordTrace (prefixWord ++ tailWord_3022782) baseStart_3022782 baseEnd_3022782 := by
    simpa [prefixWord, tailWord_3022782, baseEnd_3022782] using wordTrace_append hprefix tailTrace_3022782
  have hstable : (prefixWord ++ tailWord_3022782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022782).length < 2 ^ (prefixWord ++ tailWord_3022782).sum := by decide
  have hdescent : baseEnd_3022782 < baseStart_3022782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022795 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_3022795 : Nat := 118140960795 + 3022795 * 2 ^ 59
def prefixEnd_3022795 : Nat := 4983230072969 + 3 ^ 40 * 3022795 * 2
def baseEnd_3022795 : Nat := 1034764503338404022907283

theorem tailTrace_3022795 : CollatzResearch.WordTrace tailWord_3022795 prefixEnd_3022795 1034764503338404022907283 := by
  unfold tailWord_3022795
  simp only [CollatzResearch.WordTrace]
  refine ⟨110250391083937442130165839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73500260722624961420110559 110250391083937442130165839)
  ·
    refine ⟨165375586625906163195248759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110250391083937442130165839 165375586625906163195248759)
    ·
      refine ⟨248063379938859244792873139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165375586625906163195248759 248063379938859244792873139)
      ·
        refine ⟨372095069908288867189309709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248063379938859244792873139 372095069908288867189309709)
        ·
          refine ⟨139535651215608325195991141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372095069908288867189309709 139535651215608325195991141)
          ·
            refine ⟨26162934602926560974248339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139535651215608325195991141 26162934602926560974248339)
            ·
              refine ⟨39244401904389841461372509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26162934602926560974248339 39244401904389841461372509)
              ·
                refine ⟨14716650714146190548014691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39244401904389841461372509 14716650714146190548014691)
                ·
                  refine ⟨22074976071219285822022037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14716650714146190548014691 22074976071219285822022037)
                  ·
                    refine ⟨1034764503338404022907283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22074976071219285822022037 1034764503338404022907283)
                    ·
                      rfl

theorem cell22_3022795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_3022795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022795 prefixEnd_3022795 := by exact prefixLift 3022795
  have htrace : WordTrace (prefixWord ++ tailWord_3022795) baseStart_3022795 baseEnd_3022795 := by
    simpa [prefixWord, tailWord_3022795, baseEnd_3022795] using wordTrace_append hprefix tailTrace_3022795
  have hstable : (prefixWord ++ tailWord_3022795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022795).length < 2 ^ (prefixWord ++ tailWord_3022795).sum := by decide
  have hdescent : baseEnd_3022795 < baseStart_3022795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022846 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3022846 : Nat := 118140960795 + 3022846 * 2 ^ 59
def prefixEnd_3022846 : Nat := 4983230072969 + 3 ^ 40 * 3022846 * 2
def baseEnd_3022846 : Nat := 1034781961680656889882127

theorem tailTrace_3022846 : CollatzResearch.WordTrace tailWord_3022846 prefixEnd_3022846 1034781961680656889882127 := by
  unfold tailWord_3022846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781531400844084730034049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73501500804501785226848261 13781531400844084730034049)
  ·
    refine ⟨10336148550633063547525537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13781531400844084730034049 10336148550633063547525537)
    ·
      refine ⟨7752111412974797660644153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10336148550633063547525537 7752111412974797660644153)
      ·
        refine ⟨5814083559731098245483115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7752111412974797660644153 5814083559731098245483115)
        ·
          refine ⟨8721125339596647368224673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814083559731098245483115 8721125339596647368224673)
          ·
            refine ⟨6540844004697485526168505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721125339596647368224673 6540844004697485526168505)
            ·
              refine ⟨4905633003523114144626379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540844004697485526168505 4905633003523114144626379)
              ·
                refine ⟨7358449505284671216939569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905633003523114144626379 7358449505284671216939569)
                ·
                  refine ⟨5518837128963503412704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358449505284671216939569 5518837128963503412704677)
                  ·
                    refine ⟨1034781961680656889882127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518837128963503412704677 1034781961680656889882127)
                    ·
                      rfl

theorem cell22_3022846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3022846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022846 prefixEnd_3022846 := by exact prefixLift 3022846
  have htrace : WordTrace (prefixWord ++ tailWord_3022846) baseStart_3022846 baseEnd_3022846 := by
    simpa [prefixWord, tailWord_3022846, baseEnd_3022846] using wordTrace_append hprefix tailTrace_3022846
  have hstable : (prefixWord ++ tailWord_3022846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022846).length < 2 ^ (prefixWord ++ tailWord_3022846).sum := by decide
  have hdescent : baseEnd_3022846 < baseStart_3022846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022861 : List Nat := [1, 7, 1, 2, 1, 10]
def baseStart_3022861 : Nat := 118140960795 + 3022861 * 2 ^ 59
def prefixEnd_3022861 : Nat := 4983230072969 + 3 ^ 40 * 3022861 * 2
def baseEnd_3022861 : Nat := 12775149339348170997001

theorem tailTrace_3022861 : CollatzResearch.WordTrace tailWord_3022861 prefixEnd_3022861 12775149339348170997001 := by
  unfold tailWord_3022861
  simp only [CollatzResearch.WordTrace]
  refine ⟨110252798301698335402068437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73501865534465556934712291 110252798301698335402068437)
  ·
    refine ⟨2584049960196054735985979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110252798301698335402068437 2584049960196054735985979)
    ·
      refine ⟨3876074940294082103978969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584049960196054735985979 3876074940294082103978969)
      ·
        refine ⟨2907056205220561577984227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876074940294082103978969 2907056205220561577984227)
        ·
          refine ⟨4360584307830842366976341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907056205220561577984227 4360584307830842366976341)
          ·
            refine ⟨12775149339348170997001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4360584307830842366976341 12775149339348170997001)
            ·
              rfl

theorem cell22_3022861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 10].length) (baseStart_3022861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022861 prefixEnd_3022861 := by exact prefixLift 3022861
  have htrace : WordTrace (prefixWord ++ tailWord_3022861) baseStart_3022861 baseEnd_3022861 := by
    simpa [prefixWord, tailWord_3022861, baseEnd_3022861] using wordTrace_append hprefix tailTrace_3022861
  have hstable : (prefixWord ++ tailWord_3022861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022861).length < 2 ^ (prefixWord ++ tailWord_3022861).sum := by decide
  have hdescent : baseEnd_3022861 < baseStart_3022861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022910 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3022910 : Nat := 118140960795 + 3022910 * 2 ^ 59
def prefixEnd_3022910 : Nat := 4983230072969 + 3 ^ 40 * 3022910 * 2
def baseEnd_3022910 : Nat := 1034803870188582056281931

theorem tailTrace_3022910 : CollatzResearch.WordTrace tailWord_3022910 prefixEnd_3022910 1034803870188582056281931 := by
  unfold tailWord_3022910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781823184815102096325273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73503056985680544513734789 13781823184815102096325273)
  ·
    refine ⟨10336367388611326572243955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13781823184815102096325273 10336367388611326572243955)
    ·
      refine ⟨15504551082916989858365933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336367388611326572243955 15504551082916989858365933)
      ·
        refine ⟨5814206656093871196887225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15504551082916989858365933 5814206656093871196887225)
        ·
          refine ⟨4360654992070403397665419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5814206656093871196887225 4360654992070403397665419)
          ·
            refine ⟨6540982488105605096498129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360654992070403397665419 6540982488105605096498129)
            ·
              refine ⟨4905736866079203822373597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540982488105605096498129 4905736866079203822373597)
              ·
                refine ⟨1839651324779701433390099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4905736866079203822373597 1839651324779701433390099)
                ·
                  refine ⟨2759476987169552150085149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839651324779701433390099 2759476987169552150085149)
                  ·
                    refine ⟨1034803870188582056281931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759476987169552150085149 1034803870188582056281931)
                    ·
                      rfl

theorem cell22_3022910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3022910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022910 prefixEnd_3022910 := by exact prefixLift 3022910
  have htrace : WordTrace (prefixWord ++ tailWord_3022910) baseStart_3022910 baseEnd_3022910 := by
    simpa [prefixWord, tailWord_3022910, baseEnd_3022910] using wordTrace_append hprefix tailTrace_3022910
  have hstable : (prefixWord ++ tailWord_3022910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022910).length < 2 ^ (prefixWord ++ tailWord_3022910).sum := by decide
  have hdescent : baseEnd_3022910 < baseStart_3022910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022919 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3022919 : Nat := 118140960795 + 3022919 * 2 ^ 59
def prefixEnd_3022919 : Nat := 4983230072969 + 3 ^ 40 * 3022919 * 2
def baseEnd_3022919 : Nat := 1034806951072509032806903

theorem tailTrace_3022919 : CollatzResearch.WordTrace tailWord_3022919 prefixEnd_3022919 1034806951072509032806903 := by
  unfold tailWord_3022919
  simp only [CollatzResearch.WordTrace]
  refine ⟨110254913735488211307679811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73503275823658807538453207 110254913735488211307679811)
  ·
    refine ⟨165382370603232316961519717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110254913735488211307679811 165382370603232316961519717)
    ·
      refine ⟨31009194488106059430284947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165382370603232316961519717 31009194488106059430284947)
      ·
        refine ⟨46513791732159089145427421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31009194488106059430284947 46513791732159089145427421)
        ·
          refine ⟨17442671899559658429535283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46513791732159089145427421 17442671899559658429535283)
          ·
            refine ⟨26164007849339487644302925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17442671899559658429535283 26164007849339487644302925)
            ·
              refine ⟨9811502943502307866613597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26164007849339487644302925 9811502943502307866613597)
              ·
                refine ⟨3679313603813365449980099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9811502943502307866613597 3679313603813365449980099)
                ·
                  refine ⟨5518970405720048174970149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679313603813365449980099 5518970405720048174970149)
                  ·
                    refine ⟨1034806951072509032806903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518970405720048174970149 1034806951072509032806903)
                    ·
                      rfl

theorem cell22_3022919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3022919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022919 prefixEnd_3022919 := by exact prefixLift 3022919
  have htrace : WordTrace (prefixWord ++ tailWord_3022919) baseStart_3022919 baseEnd_3022919 := by
    simpa [prefixWord, tailWord_3022919, baseEnd_3022919] using wordTrace_append hprefix tailTrace_3022919
  have hstable : (prefixWord ++ tailWord_3022919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022919).length < 2 ^ (prefixWord ++ tailWord_3022919).sum := by decide
  have hdescent : baseEnd_3022919 < baseStart_3022919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022947 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_3022947 : Nat := 118140960795 + 3022947 * 2 ^ 59
def prefixEnd_3022947 : Nat := 4983230072969 + 3 ^ 40 * 3022947 * 2
def baseEnd_3022947 : Nat := 1034816536044726293106817

theorem tailTrace_3022947 : CollatzResearch.WordTrace tailWord_3022947 prefixEnd_3022947 1034816536044726293106817 := by
  unfold tailWord_3022947
  simp only [CollatzResearch.WordTrace]
  refine ⟨110255934979386772089699095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73503956652924514726466063 110255934979386772089699095)
  ·
    refine ⟨165383902469080158134548643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110255934979386772089699095 165383902469080158134548643)
    ·
      refine ⟨248075853703620237201822965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165383902469080158134548643 248075853703620237201822965)
      ·
        refine ⟨23257111284714397237670903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248075853703620237201822965 23257111284714397237670903)
        ·
          refine ⟨34885666927071595856506355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23257111284714397237670903 34885666927071595856506355)
          ·
            refine ⟨52328500390607393784759533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34885666927071595856506355 52328500390607393784759533)
            ·
              refine ⟨19623187646477772669284825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52328500390607393784759533 19623187646477772669284825)
              ·
                refine ⟨14717390734858329501963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19623187646477772669284825 14717390734858329501963619)
                ·
                  refine ⟨22076086102287494252945429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14717390734858329501963619 22076086102287494252945429)
                  ·
                    refine ⟨1034816536044726293106817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22076086102287494252945429 1034816536044726293106817)
                    ·
                      rfl

theorem cell22_3022947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_3022947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022947 prefixEnd_3022947 := by exact prefixLift 3022947
  have htrace : WordTrace (prefixWord ++ tailWord_3022947) baseStart_3022947 baseEnd_3022947 := by
    simpa [prefixWord, tailWord_3022947, baseEnd_3022947] using wordTrace_append hprefix tailTrace_3022947
  have hstable : (prefixWord ++ tailWord_3022947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022947).length < 2 ^ (prefixWord ++ tailWord_3022947).sum := by decide
  have hdescent : baseEnd_3022947 < baseStart_3022947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022949 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_3022949 : Nat := 118140960795 + 3022949 * 2 ^ 59
def prefixEnd_3022949 : Nat := 4983230072969 + 3 ^ 40 * 3022949 * 2
def baseEnd_3022949 : Nat := 1034817220685598954556811

theorem tailTrace_3022949 : CollatzResearch.WordTrace tailWord_3022949 prefixEnd_3022949 1034817220685598954556811 := by
  unfold tailWord_3022949
  simp only [CollatzResearch.WordTrace]
  refine ⟨110256007925379526431271901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73504005283586350954181267 110256007925379526431271901)
  ·
    refine ⟨41346002972017322411726963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110256007925379526431271901 41346002972017322411726963)
    ·
      refine ⟨62019004458025983617590445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41346002972017322411726963 62019004458025983617590445)
      ·
        refine ⟨23257126671759743856596417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62019004458025983617590445 23257126671759743856596417)
        ·
          refine ⟨17442845003819807892447313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23257126671759743856596417 17442845003819807892447313)
          ·
            refine ⟨13082133752864855919335485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17442845003819807892447313 13082133752864855919335485)
            ·
              refine ⟨4905800157324320969750807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13082133752864855919335485 4905800157324320969750807)
              ·
                refine ⟨7358700235986481454626211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905800157324320969750807 7358700235986481454626211)
                ·
                  refine ⟨11038050353979722181939317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7358700235986481454626211 11038050353979722181939317)
                  ·
                    refine ⟨1034817220685598954556811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038050353979722181939317 1034817220685598954556811)
                    ·
                      rfl

theorem cell22_3022949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_3022949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022949 prefixEnd_3022949 := by exact prefixLift 3022949
  have htrace : WordTrace (prefixWord ++ tailWord_3022949) baseStart_3022949 baseEnd_3022949 := by
    simpa [prefixWord, tailWord_3022949, baseEnd_3022949] using wordTrace_append hprefix tailTrace_3022949
  have hstable : (prefixWord ++ tailWord_3022949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022949).length < 2 ^ (prefixWord ++ tailWord_3022949).sum := by decide
  have hdescent : baseEnd_3022949 < baseStart_3022949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022966 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3022966 : Nat := 118140960795 + 3022966 * 2 ^ 59
def prefixEnd_3022966 : Nat := 4983230072969 + 3 ^ 40 * 3022966 * 2
def baseEnd_3022966 : Nat := 1034823040133016576881759

theorem tailTrace_3022966 : CollatzResearch.WordTrace tailWord_3022966 prefixEnd_3022966 1034823040133016576881759 := by
  unfold tailWord_3022966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891039247894871145915047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73504418644211958889760501 6891039247894871145915047)
  ·
    refine ⟨10336558871842306718872571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891039247894871145915047 10336558871842306718872571)
    ·
      refine ⟨15504838307763460078308857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336558871842306718872571 15504838307763460078308857)
      ·
        refine ⟨11628628730822595058731643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15504838307763460078308857 11628628730822595058731643)
        ·
          refine ⟨17442943096233892588097465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628628730822595058731643 17442943096233892588097465)
          ·
            refine ⟨13082207322175419441073099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17442943096233892588097465 13082207322175419441073099)
            ·
              refine ⟨19623310983263129161609649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13082207322175419441073099 19623310983263129161609649)
              ·
                refine ⟨14717483237447346871207237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19623310983263129161609649 14717483237447346871207237)
                ·
                  refine ⟨2759528107021377538351357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14717483237447346871207237 2759528107021377538351357)
                  ·
                    refine ⟨1034823040133016576881759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759528107021377538351357 1034823040133016576881759)
                    ·
                      rfl

theorem cell22_3022966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3022966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022966 prefixEnd_3022966 := by exact prefixLift 3022966
  have htrace : WordTrace (prefixWord ++ tailWord_3022966) baseStart_3022966 baseEnd_3022966 := by
    simpa [prefixWord, tailWord_3022966, baseEnd_3022966] using wordTrace_append hprefix tailTrace_3022966
  have hstable : (prefixWord ++ tailWord_3022966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022966).length < 2 ^ (prefixWord ++ tailWord_3022966).sum := by decide
  have hdescent : baseEnd_3022966 < baseStart_3022966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022992 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_3022992 : Nat := 118140960795 + 3022992 * 2 ^ 59
def prefixEnd_3022992 : Nat := 4983230072969 + 3 ^ 40 * 3022992 * 2
def baseEnd_3022992 : Nat := 1034831940464361175731679

theorem tailTrace_3022992 : CollatzResearch.WordTrace tailWord_3022992 prefixEnd_3022992 1034831940464361175731679 := by
  unfold tailWord_3022992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55128788132111872387543615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73505050842815829850058153 55128788132111872387543615)
  ·
    refine ⟨82693182198167808581315423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55128788132111872387543615 82693182198167808581315423)
    ·
      refine ⟨124039773297251712871973135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82693182198167808581315423 124039773297251712871973135)
      ·
        refine ⟨186059659945877569307959703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124039773297251712871973135 186059659945877569307959703)
        ·
          refine ⟨279089489918816353961939555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186059659945877569307959703 279089489918816353961939555)
          ·
            refine ⟨418634234878224530942909333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279089489918816353961939555 418634234878224530942909333)
            ·
              refine ⟨19623479759916774887948875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 418634234878224530942909333 19623479759916774887948875)
              ·
                refine ⟨29435219639875162331923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19623479759916774887948875 29435219639875162331923313)
                ·
                  refine ⟨22076414729906371748942485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29435219639875162331923313 22076414729906371748942485)
                  ·
                    refine ⟨1034831940464361175731679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22076414729906371748942485 1034831940464361175731679)
                    ·
                      rfl

theorem cell22_3022992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_3022992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022992 prefixEnd_3022992 := by exact prefixLift 3022992
  have htrace : WordTrace (prefixWord ++ tailWord_3022992) baseStart_3022992 baseEnd_3022992 := by
    simpa [prefixWord, tailWord_3022992, baseEnd_3022992] using wordTrace_append hprefix tailTrace_3022992
  have hstable : (prefixWord ++ tailWord_3022992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022992).length < 2 ^ (prefixWord ++ tailWord_3022992).sum := by decide
  have hdescent : baseEnd_3022992 < baseStart_3022992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023000 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_3023000 : Nat := 118140960795 + 3023000 * 2 ^ 59
def prefixEnd_3023000 : Nat := 4983230072969 + 3 ^ 40 * 3023000 * 2
def baseEnd_3023000 : Nat := 1034834679027851821531655

theorem tailTrace_3023000 : CollatzResearch.WordTrace tailWord_3023000 prefixEnd_3023000 1034834679027851821531655 := by
  unfold tailWord_3023000
  simp only [CollatzResearch.WordTrace]
  refine ⟨55128934024097381070689227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73505245365463174760918969 55128934024097381070689227)
  ·
    refine ⟨82693401036146071606033841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55128934024097381070689227 82693401036146071606033841)
    ·
      refine ⟨62020050777109553704525381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82693401036146071606033841 62020050777109553704525381)
      ·
        refine ⟨11628759520708041319598509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62020050777109553704525381 11628759520708041319598509)
        ·
          refine ⟨4360784820265515494849441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11628759520708041319598509 4360784820265515494849441)
          ·
            refine ⟨3270588615199136621137081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360784820265515494849441 3270588615199136621137081)
            ·
              refine ⟨2452941461399352465852811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270588615199136621137081 2452941461399352465852811)
              ·
                refine ⟨3679412192099028698779217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452941461399352465852811 3679412192099028698779217)
                ·
                  refine ⟨2759559144074271524084413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679412192099028698779217 2759559144074271524084413)
                  ·
                    refine ⟨1034834679027851821531655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759559144074271524084413 1034834679027851821531655)
                    ·
                      rfl

theorem cell22_3023000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_3023000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023000 prefixEnd_3023000 := by exact prefixLift 3023000
  have htrace : WordTrace (prefixWord ++ tailWord_3023000) baseStart_3023000 baseEnd_3023000 := by
    simpa [prefixWord, tailWord_3023000, baseEnd_3023000] using wordTrace_append hprefix tailTrace_3023000
  have hstable : (prefixWord ++ tailWord_3023000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023000).length < 2 ^ (prefixWord ++ tailWord_3023000).sum := by decide
  have hdescent : baseEnd_3023000 < baseStart_3023000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023084 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_3023084 : Nat := 118140960795 + 3023084 * 2 ^ 59
def prefixEnd_3023084 : Nat := 4983230072969 + 3 ^ 40 * 3023084 * 2
def baseEnd_3023084 : Nat := 1034863433944503602431397

theorem tailTrace_3023084 : CollatzResearch.WordTrace tailWord_3023084 prefixEnd_3023084 1034863433944503602431397 := by
  unfold tailWord_3023084
  simp only [CollatzResearch.WordTrace]
  refine ⟨55130465889945222243718153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73507287853260296324957537 55130465889945222243718153)
  ·
    refine ⟨41347849417458916682788615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55130465889945222243718153 41347849417458916682788615)
    ·
      refine ⟨62021774126188375024182923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41347849417458916682788615 62021774126188375024182923)
      ·
        refine ⟨93032661189282562536274385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62021774126188375024182923 93032661189282562536274385)
        ·
          refine ⟨69774495891961921902205789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93032661189282562536274385 69774495891961921902205789)
          ·
            refine ⟨26165435959485720713327171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69774495891961921902205789 26165435959485720713327171)
            ·
              refine ⟨39248153939228581069990757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26165435959485720713327171 39248153939228581069990757)
              ·
                refine ⟨7359028863605358950623267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39248153939228581069990757 7359028863605358950623267)
                ·
                  refine ⟨11038543295408038425934901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359028863605358950623267 11038543295408038425934901)
                  ·
                    refine ⟨1034863433944503602431397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038543295408038425934901 1034863433944503602431397)
                    ·
                      rfl

theorem cell22_3023084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_3023084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023084 prefixEnd_3023084 := by exact prefixLift 3023084
  have htrace : WordTrace (prefixWord ++ tailWord_3023084) baseStart_3023084 baseEnd_3023084 := by
    simpa [prefixWord, tailWord_3023084, baseEnd_3023084] using wordTrace_append hprefix tailTrace_3023084
  have hstable : (prefixWord ++ tailWord_3023084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023084).length < 2 ^ (prefixWord ++ tailWord_3023084).sum := by decide
  have hdescent : baseEnd_3023084 < baseStart_3023084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023150 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3023150 : Nat := 118140960795 + 3023150 * 2 ^ 59
def prefixEnd_3023150 : Nat := 4983230072969 + 3 ^ 40 * 3023150 * 2
def baseEnd_3023150 : Nat := 1034886027093301430281195

theorem tailTrace_3023150 : CollatzResearch.WordTrace tailWord_3023150 prefixEnd_3023150 1034886027093301430281195 := by
  unfold tailWord_3023150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782917374706417219917363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73508892665100891839559269 13782917374706417219917363)
  ·
    refine ⟨20674376062059625829876045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13782917374706417219917363 20674376062059625829876045)
    ·
      refine ⟨7752891023272359686203517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20674376062059625829876045 7752891023272359686203517)
      ·
        refine ⟨2907334133727134882326319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7752891023272359686203517 2907334133727134882326319)
        ·
          refine ⟨4361001200590702323489479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907334133727134882326319 4361001200590702323489479)
          ·
            refine ⟨6541501800886053485234219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361001200590702323489479 6541501800886053485234219)
            ·
              refine ⟨9812252701329080227851329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541501800886053485234219 9812252701329080227851329)
              ·
                refine ⟨7359189525996810170888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9812252701329080227851329 7359189525996810170888497)
                ·
                  refine ⟨5519392144497607628166373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7359189525996810170888497 5519392144497607628166373)
                  ·
                    refine ⟨1034886027093301430281195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519392144497607628166373 1034886027093301430281195)
                    ·
                      rfl

theorem cell22_3023150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3023150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023150 prefixEnd_3023150 := by exact prefixLift 3023150
  have htrace : WordTrace (prefixWord ++ tailWord_3023150) baseStart_3023150 baseEnd_3023150 := by
    simpa [prefixWord, tailWord_3023150, baseEnd_3023150] using wordTrace_append hprefix tailTrace_3023150
  have hstable : (prefixWord ++ tailWord_3023150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023150).length < 2 ^ (prefixWord ++ tailWord_3023150).sum := by decide
  have hdescent : baseEnd_3023150 < baseStart_3023150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023169 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3023169 : Nat := 118140960795 + 3023169 * 2 ^ 59
def prefixEnd_3023169 : Nat := 4983230072969 + 3 ^ 40 * 3023169 * 2
def baseEnd_3023169 : Nat := 1034892531181591714056137

theorem tailTrace_3023169 : CollatzResearch.WordTrace tailWord_3023169 prefixEnd_3023169 1034892531181591714056137 := by
  unfold tailWord_3023169
  simp only [CollatzResearch.WordTrace]
  refine ⟨110264031984582504004280561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73509354656388336002853707 110264031984582504004280561)
  ·
    refine ⟨82698023988436878003210421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110264031984582504004280561 82698023988436878003210421)
    ·
      refine ⟨7752939748915957312800977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82698023988436878003210421 7752939748915957312800977)
      ·
        refine ⟨5814704811686967984600733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7752939748915957312800977 5814704811686967984600733)
        ·
          refine ⟨2180514304382612994225275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5814704811686967984600733 2180514304382612994225275)
          ·
            refine ⟨3270771456573919491337913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180514304382612994225275 3270771456573919491337913)
            ·
              refine ⟨2453078592430439618503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270771456573919491337913 2453078592430439618503435)
              ·
                refine ⟨3679617888645659427755153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453078592430439618503435 3679617888645659427755153)
                ·
                  refine ⟨2759713416484244570816365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679617888645659427755153 2759713416484244570816365)
                  ·
                    refine ⟨1034892531181591714056137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759713416484244570816365 1034892531181591714056137)
                    ·
                      rfl

theorem cell22_3023169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3023169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023169 prefixEnd_3023169 := by exact prefixLift 3023169
  have htrace : WordTrace (prefixWord ++ tailWord_3023169) baseStart_3023169 baseEnd_3023169 := by
    simpa [prefixWord, tailWord_3023169, baseEnd_3023169] using wordTrace_append hprefix tailTrace_3023169
  have hstable : (prefixWord ++ tailWord_3023169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023169).length < 2 ^ (prefixWord ++ tailWord_3023169).sum := by decide
  have hdescent : baseEnd_3023169 < baseStart_3023169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023266 : List Nat := [3, 3, 1, 2, 1, 1, 11]
def baseStart_3023266 : Nat := 118140960795 + 3023266 * 2 ^ 59
def prefixEnd_3023266 : Nat := 4983230072969 + 3 ^ 40 * 3023266 * 2
def baseEnd_3023266 : Nat := 38330582824589473865957

theorem tailTrace_3023266 : CollatzResearch.WordTrace tailWord_3023266 prefixEnd_3023266 38330582824589473865957 := by
  unfold tailWord_3023266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566892466307772392640413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73511713243487393047041101 27566892466307772392640413)
  ·
    refine ⟨10337584674865414647240155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27566892466307772392640413 10337584674865414647240155)
    ·
      refine ⟨15506377012298121970860233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337584674865414647240155 15506377012298121970860233)
      ·
        refine ⟨11629782759223591478145175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15506377012298121970860233 11629782759223591478145175)
        ·
          refine ⟨17444674138835387217217763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11629782759223591478145175 17444674138835387217217763)
          ·
            refine ⟨26167011208253080825826645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17444674138835387217217763 26167011208253080825826645)
            ·
              refine ⟨38330582824589473865957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26167011208253080825826645 38330582824589473865957)
              ·
                rfl

theorem cell22_3023266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 11].length) (baseStart_3023266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023266 prefixEnd_3023266 := by exact prefixLift 3023266
  have htrace : WordTrace (prefixWord ++ tailWord_3023266) baseStart_3023266 baseEnd_3023266 := by
    simpa [prefixWord, tailWord_3023266, baseEnd_3023266] using wordTrace_append hprefix tailTrace_3023266
  have hstable : (prefixWord ++ tailWord_3023266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023266).length < 2 ^ (prefixWord ++ tailWord_3023266).sum := by decide
  have hdescent : baseEnd_3023266 < baseStart_3023266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023356 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3023356 : Nat := 118140960795 + 3023356 * 2 ^ 59
def prefixEnd_3023356 : Nat := 4983230072969 + 3 ^ 40 * 3023356 * 2
def baseEnd_3023356 : Nat := 344985515034395186543521

theorem tailTrace_3023356 : CollatzResearch.WordTrace tailWord_3023356 prefixEnd_3023356 344985515034395186543521 := by
  unfold tailWord_3023356
  simp only [CollatzResearch.WordTrace]
  refine ⟨55135426217452517470668961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73513901623270023294225281 55135426217452517470668961)
  ·
    refine ⟨41351569663089388103001721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55135426217452517470668961 41351569663089388103001721)
    ·
      refine ⟨31013677247317041077251291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41351569663089388103001721 31013677247317041077251291)
      ·
        refine ⟨46520515870975561615876937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31013677247317041077251291 46520515870975561615876937)
        ·
          refine ⟨34890386903231671211907703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46520515870975561615876937 34890386903231671211907703)
          ·
            refine ⟨52335580354847506817861555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34890386903231671211907703 52335580354847506817861555)
            ·
              refine ⟨78503370532271260226792333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52335580354847506817861555 78503370532271260226792333)
              ·
                refine ⟨29438763949601722585047125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78503370532271260226792333 29438763949601722585047125)
                ·
                  refine ⟨344985515034395186543521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29438763949601722585047125 344985515034395186543521)
                  ·
                    rfl

theorem cell22_3023356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3023356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023356 prefixEnd_3023356 := by exact prefixLift 3023356
  have htrace : WordTrace (prefixWord ++ tailWord_3023356) baseStart_3023356 baseEnd_3023356 := by
    simpa [prefixWord, tailWord_3023356, baseEnd_3023356] using wordTrace_append hprefix tailTrace_3023356
  have hstable : (prefixWord ++ tailWord_3023356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023356).length < 2 ^ (prefixWord ++ tailWord_3023356).sum := by decide
  have hdescent : baseEnd_3023356 < baseStart_3023356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023383 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 1, 3]
def baseStart_3023383 : Nat := 118140960795 + 3023383 * 2 ^ 59
def prefixEnd_3023383 : Nat := 4983230072969 + 3 ^ 40 * 3023383 * 2
def baseEnd_3023383 : Nat := 1034965787754966489205481

theorem tailTrace_3023383 : CollatzResearch.WordTrace tailWord_3023383 prefixEnd_3023383 1034965787754966489205481 := by
  unfold tailWord_3023383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110271837205807218552570803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73514558137204812368380535 110271837205807218552570803)
  ·
    refine ⟨165407755808710827828856205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110271837205807218552570803 165407755808710827828856205)
    ·
      refine ⟨62027908428266560435821077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165407755808710827828856205 62027908428266560435821077)
      ·
        refine ⟨2907558207574995020429113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62027908428266560435821077 2907558207574995020429113)
        ·
          refine ⟨2180668655681246265321835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907558207574995020429113 2180668655681246265321835)
          ·
            refine ⟨3271002983521869397982753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180668655681246265321835 3271002983521869397982753)
            ·
              refine ⟨2453252237641402048487065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271002983521869397982753 2453252237641402048487065)
              ·
                refine ⟨1839939178231051536365299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453252237641402048487065 1839939178231051536365299)
                ·
                  refine ⟨2759908767346577304547949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839939178231051536365299 2759908767346577304547949)
                  ·
                    refine ⟨1034965787754966489205481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759908767346577304547949 1034965787754966489205481)
                    ·
                      rfl

theorem cell22_3023383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_3023383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023383 prefixEnd_3023383 := by exact prefixLift 3023383
  have htrace : WordTrace (prefixWord ++ tailWord_3023383) baseStart_3023383 baseEnd_3023383 := by
    simpa [prefixWord, tailWord_3023383, baseEnd_3023383] using wordTrace_append hprefix tailTrace_3023383
  have hstable : (prefixWord ++ tailWord_3023383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023383).length < 2 ^ (prefixWord ++ tailWord_3023383).sum := by decide
  have hdescent : baseEnd_3023383 < baseStart_3023383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023420 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3023420 : Nat := 118140960795 + 3023420 * 2 ^ 59
def prefixEnd_3023420 : Nat := 4983230072969 + 3 ^ 40 * 3023420 * 2
def baseEnd_3023420 : Nat := 1034978453611110726030367

theorem tailTrace_3023420 : CollatzResearch.WordTrace tailWord_3023420 prefixEnd_3023420 1034978453611110726030367 := by
  unfold tailWord_3023420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136593353336586935833857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73515457804448782581111809 55136593353336586935833857)
  ·
    refine ⟨41352445015002440201875393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55136593353336586935833857 41352445015002440201875393)
    ·
      refine ⟨31014333761251830151406545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41352445015002440201875393 31014333761251830151406545)
      ·
        refine ⟨23260750320938872613554909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31014333761251830151406545 23260750320938872613554909)
        ·
          refine ⟨8722781370352077230083091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23260750320938872613554909 8722781370352077230083091)
          ·
            refine ⟨13084172055528115845124637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722781370352077230083091 13084172055528115845124637)
            ·
              refine ⟨4906564520823043441921739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13084172055528115845124637 4906564520823043441921739)
              ·
                refine ⟨7359846781234565162882609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906564520823043441921739 7359846781234565162882609)
                ·
                  refine ⟨5519885085925923872161957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7359846781234565162882609 5519885085925923872161957)
                  ·
                    refine ⟨1034978453611110726030367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519885085925923872161957 1034978453611110726030367)
                    ·
                      rfl

theorem cell22_3023420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3023420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023420 prefixEnd_3023420 := by exact prefixLift 3023420
  have htrace : WordTrace (prefixWord ++ tailWord_3023420) baseStart_3023420 baseEnd_3023420 := by
    simpa [prefixWord, tailWord_3023420, baseEnd_3023420] using wordTrace_append hprefix tailTrace_3023420
  have hstable : (prefixWord ++ tailWord_3023420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023420).length < 2 ^ (prefixWord ++ tailWord_3023420).sum := by decide
  have hdescent : baseEnd_3023420 < baseStart_3023420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023587 : List Nat := [1, 1, 1, 7, 1, 2, 3, 6]
def baseStart_3023587 : Nat := 118140960795 + 3023587 * 2 ^ 59
def prefixEnd_3023587 : Nat := 4983230072969 + 3 ^ 40 * 3023587 * 2
def baseEnd_3023587 : Nat := 115003957902664217456095

theorem tailTrace_3023587 : CollatzResearch.WordTrace tailWord_3023587 prefixEnd_3023587 115003957902664217456095 := by
  unfold tailWord_3023587
  simp only [CollatzResearch.WordTrace]
  refine ⟨110279277697068161392997015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73519518464712107595331343 110279277697068161392997015)
  ·
    refine ⟨165418916545602242089495523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110279277697068161392997015 165418916545602242089495523)
    ·
      refine ⟨248128374818403363134243285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165418916545602242089495523 248128374818403363134243285)
      ·
        refine ⟨5815508784806328823458827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 248128374818403363134243285 5815508784806328823458827)
        ·
          refine ⟨8723263177209493235188241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815508784806328823458827 8723263177209493235188241)
          ·
            refine ⟨6542447382907119926391181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723263177209493235188241 6542447382907119926391181)
            ·
              refine ⟨2453417768590169972396693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6542447382907119926391181 2453417768590169972396693)
              ·
                refine ⟨115003957902664217456095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2453417768590169972396693 115003957902664217456095)
                ·
                  rfl

theorem cell22_3023587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 6].length) (baseStart_3023587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023587 prefixEnd_3023587 := by exact prefixLift 3023587
  have htrace : WordTrace (prefixWord ++ tailWord_3023587) baseStart_3023587 baseEnd_3023587 := by
    simpa [prefixWord, tailWord_3023587, baseEnd_3023587] using wordTrace_append hprefix tailTrace_3023587
  have hstable : (prefixWord ++ tailWord_3023587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023587).length < 2 ^ (prefixWord ++ tailWord_3023587).sum := by decide
  have hdescent : baseEnd_3023587 < baseStart_3023587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023604 : List Nat := [2, 6, 1, 1, 2, 1, 9]
def baseStart_3023604 : Nat := 118140960795 + 3023604 * 2 ^ 59
def prefixEnd_3023604 : Nat := 4983230072969 + 3 ^ 40 * 3023604 * 2
def baseEnd_3023604 : Nat := 38334868169310947386289

theorem tailTrace_3023604 : CollatzResearch.WordTrace tailWord_3023604 prefixEnd_3023604 38334868169310947386289 := by
  unfold tailWord_3023604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55139948869003286648182933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73519931825337715530910577 55139948869003286648182933)
  ·
    refine ⟨2584685103234529061633575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55139948869003286648182933 2584685103234529061633575)
    ·
      refine ⟨3877027654851793592450363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584685103234529061633575 3877027654851793592450363)
      ·
        refine ⟨5815541482277690388675545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877027654851793592450363 5815541482277690388675545)
        ·
          refine ⟨4361656111708267791506659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5815541482277690388675545 4361656111708267791506659)
          ·
            refine ⟨6542484167562401687259989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361656111708267791506659 6542484167562401687259989)
            ·
              refine ⟨38334868169310947386289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6542484167562401687259989 38334868169310947386289)
              ·
                rfl

theorem cell22_3023604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 9].length) (baseStart_3023604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023604 prefixEnd_3023604 := by exact prefixLift 3023604
  have htrace : WordTrace (prefixWord ++ tailWord_3023604) baseStart_3023604 baseEnd_3023604 := by
    simpa [prefixWord, tailWord_3023604, baseEnd_3023604] using wordTrace_append hprefix tailTrace_3023604
  have hstable : (prefixWord ++ tailWord_3023604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023604).length < 2 ^ (prefixWord ++ tailWord_3023604).sum := by decide
  have hdescent : baseEnd_3023604 < baseStart_3023604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023670 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3023670 : Nat := 118140960795 + 3023670 * 2 ^ 59
def prefixEnd_3023670 : Nat := 4983230072969 + 3 ^ 40 * 3023670 * 2
def baseEnd_3023670 : Nat := 1035064033720193407279601

theorem tailTrace_3023670 : CollatzResearch.WordTrace tailWord_3023670 prefixEnd_3023670 1035064033720193407279601 := by
  unfold tailWord_3023670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892644059735466660516779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73521536637178311045512309 6892644059735466660516779)
  ·
    refine ⟨10338966089603199990775169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892644059735466660516779 10338966089603199990775169)
    ·
      refine ⟨7754224567202399993081377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10338966089603199990775169 7754224567202399993081377)
      ·
        refine ⟨5815668425401799994811033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7754224567202399993081377 5815668425401799994811033)
        ·
          refine ⟨4361751319051349996108275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5815668425401799994811033 4361751319051349996108275)
          ·
            refine ⟨6542626978577024994162413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361751319051349996108275 6542626978577024994162413)
            ·
              refine ⟨2453485116966384372810905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6542626978577024994162413 2453485116966384372810905)
              ·
                refine ⟨1840113837724788279608179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453485116966384372810905 1840113837724788279608179)
                ·
                  refine ⟨2760170756587182419412269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840113837724788279608179 2760170756587182419412269)
                  ·
                    refine ⟨1035064033720193407279601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760170756587182419412269 1035064033720193407279601)
                    ·
                      rfl

theorem cell22_3023670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3023670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023670 prefixEnd_3023670 := by exact prefixLift 3023670
  have htrace : WordTrace (prefixWord ++ tailWord_3023670) baseStart_3023670 baseEnd_3023670 := by
    simpa [prefixWord, tailWord_3023670, baseEnd_3023670] using wordTrace_append hprefix tailTrace_3023670
  have hstable : (prefixWord ++ tailWord_3023670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023670).length < 2 ^ (prefixWord ++ tailWord_3023670).sum := by decide
  have hdescent : baseEnd_3023670 < baseStart_3023670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023690 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3023690 : Nat := 118140960795 + 3023690 * 2 ^ 59
def prefixEnd_3023690 : Nat := 4983230072969 + 3 ^ 40 * 3023690 * 2
def baseEnd_3023690 : Nat := 1035070880128920021779539

theorem tailTrace_3023690 : CollatzResearch.WordTrace tailWord_3023690 prefixEnd_3023690 1035070880128920021779539 := by
  unfold tailWord_3023690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570758603923752495999131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73522022943796673322664349 27570758603923752495999131)
  ·
    refine ⟨41356137905885628743998697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27570758603923752495999131 41356137905885628743998697)
    ·
      refine ⟨31017103429414221557999023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41356137905885628743998697 31017103429414221557999023)
      ·
        refine ⟨46525655144121332336998535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31017103429414221557999023 46525655144121332336998535)
        ·
          refine ⟨69788482716181998505497803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46525655144121332336998535 69788482716181998505497803)
          ·
            refine ⟨104682724074272997758246705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69788482716181998505497803 104682724074272997758246705)
            ·
              refine ⟨78512043055704748318685029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104682724074272997758246705 78512043055704748318685029)
              ·
                refine ⟨14721008072944640309753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78512043055704748318685029 14721008072944640309753443)
                ·
                  refine ⟨22081512109416960464630165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14721008072944640309753443 22081512109416960464630165)
                  ·
                    refine ⟨1035070880128920021779539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22081512109416960464630165 1035070880128920021779539)
                    ·
                      rfl

theorem cell22_3023690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3023690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023690 prefixEnd_3023690 := by exact prefixLift 3023690
  have htrace : WordTrace (prefixWord ++ tailWord_3023690) baseStart_3023690 baseEnd_3023690 := by
    simpa [prefixWord, tailWord_3023690, baseEnd_3023690] using wordTrace_append hprefix tailTrace_3023690
  have hstable : (prefixWord ++ tailWord_3023690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023690).length < 2 ^ (prefixWord ++ tailWord_3023690).sum := by decide
  have hdescent : baseEnd_3023690 < baseStart_3023690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023705 : List Nat := [1, 2, 1, 2, 2, 4, 2, 8]
def baseStart_3023705 : Nat := 118140960795 + 3023705 * 2 ^ 59
def prefixEnd_3023705 : Nat := 4983230072969 + 3 ^ 40 * 3023705 * 2
def baseEnd_3023705 : Nat := 115008446103940553628277

theorem tailTrace_3023705 : CollatzResearch.WordTrace tailWord_3023705 prefixEnd_3023705 115008446103940553628277 := by
  unfold tailWord_3023705
  simp only [CollatzResearch.WordTrace]
  refine ⟨110283581510640667545792569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73522387673760445030528379 110283581510640667545792569)
  ·
    refine ⟨82712686132980500659344427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110283581510640667545792569 82712686132980500659344427)
    ·
      refine ⟨124069029199470750989016641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82712686132980500659344427 124069029199470750989016641)
      ·
        refine ⟨93051771899603063241762481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124069029199470750989016641 93051771899603063241762481)
        ·
          refine ⟨69788828924702297431321861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93051771899603063241762481 69788828924702297431321861)
          ·
            refine ⟨13085405423381680768372849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69788828924702297431321861 13085405423381680768372849)
            ·
              refine ⟨9814054067536260576279637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13085405423381680768372849 9814054067536260576279637)
              ·
                refine ⟨115008446103940553628277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9814054067536260576279637 115008446103940553628277)
                ·
                  rfl

theorem cell22_3023705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 8].length) (baseStart_3023705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023705 prefixEnd_3023705 := by exact prefixLift 3023705
  have htrace : WordTrace (prefixWord ++ tailWord_3023705) baseStart_3023705 baseEnd_3023705 := by
    simpa [prefixWord, tailWord_3023705, baseEnd_3023705] using wordTrace_append hprefix tailTrace_3023705
  have hstable : (prefixWord ++ tailWord_3023705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023705).length < 2 ^ (prefixWord ++ tailWord_3023705).sum := by decide
  have hdescent : baseEnd_3023705 < baseStart_3023705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023754 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_3023754 : Nat := 118140960795 + 3023754 * 2 ^ 59
def prefixEnd_3023754 : Nat := 4983230072969 + 3 ^ 40 * 3023754 * 2
def baseEnd_3023754 : Nat := 1035092788636845188179343

theorem tailTrace_3023754 : CollatzResearch.WordTrace tailWord_3023754 prefixEnd_3023754 1035092788636845188179343 := by
  unfold tailWord_3023754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27571342171865787228581579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73523579124975432609550877 27571342171865787228581579)
  ·
    refine ⟨41357013257798680842872369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27571342171865787228581579 41357013257798680842872369)
    ·
      refine ⟨31017759943349010632154277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41357013257798680842872369 31017759943349010632154277)
      ·
        refine ⟨5815829989377939493528927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31017759943349010632154277 5815829989377939493528927)
        ·
          refine ⟨8723744984066909240293391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815829989377939493528927 8723744984066909240293391)
          ·
            refine ⟨13085617476100363860440087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723744984066909240293391 13085617476100363860440087)
            ·
              refine ⟨19628426214150545790660131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085617476100363860440087 19628426214150545790660131)
              ·
                refine ⟨29442639321225818685990197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19628426214150545790660131 29442639321225818685990197)
                ·
                  refine ⟨2760247436364920501811581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29442639321225818685990197 2760247436364920501811581)
                  ·
                    refine ⟨1035092788636845188179343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760247436364920501811581 1035092788636845188179343)
                    ·
                      rfl

theorem cell22_3023754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_3023754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023754 prefixEnd_3023754 := by exact prefixLift 3023754
  have htrace : WordTrace (prefixWord ++ tailWord_3023754) baseStart_3023754 baseEnd_3023754 := by
    simpa [prefixWord, tailWord_3023754, baseEnd_3023754] using wordTrace_append hprefix tailTrace_3023754
  have hstable : (prefixWord ++ tailWord_3023754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023754).length < 2 ^ (prefixWord ++ tailWord_3023754).sum := by decide
  have hdescent : baseEnd_3023754 < baseStart_3023754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023857 : List Nat := [1, 2, 2, 2, 4, 1, 1, 9]
def baseStart_3023857 : Nat := 118140960795 + 3023857 * 2 ^ 59
def prefixEnd_3023857 : Nat := 4983230072969 + 3 ^ 40 * 3023857 * 2
def baseEnd_3023857 : Nat := 115014227515754139206003

theorem tailTrace_3023857 : CollatzResearch.WordTrace tailWord_3023857 prefixEnd_3023857 115014227515754139206003 := by
  unfold tailWord_3023857
  simp only [CollatzResearch.WordTrace]
  refine ⟨110289125406089997505325825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73526083604059998336883883 110289125406089997505325825)
  ·
    refine ⟨82716844054567498128994369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110289125406089997505325825 82716844054567498128994369)
    ·
      refine ⟨62037633040925623596745777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82716844054567498128994369 62037633040925623596745777)
      ·
        refine ⟨46528224780694217697559333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62037633040925623596745777 46528224780694217697559333)
        ·
          refine ⟨8724042146380165818292375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46528224780694217697559333 8724042146380165818292375)
          ·
            refine ⟨13086063219570248727438563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724042146380165818292375 13086063219570248727438563)
            ·
              refine ⟨19629094829355373091157845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13086063219570248727438563 19629094829355373091157845)
              ·
                refine ⟨115014227515754139206003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19629094829355373091157845 115014227515754139206003)
                ·
                  rfl

theorem cell22_3023857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 9].length) (baseStart_3023857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3023857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3023857 prefixEnd_3023857 := by exact prefixLift 3023857
  have htrace : WordTrace (prefixWord ++ tailWord_3023857) baseStart_3023857 baseEnd_3023857 := by
    simpa [prefixWord, tailWord_3023857, baseEnd_3023857] using wordTrace_append hprefix tailTrace_3023857
  have hstable : (prefixWord ++ tailWord_3023857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023857).length < 2 ^ (prefixWord ++ tailWord_3023857).sum := by decide
  have hdescent : baseEnd_3023857 < baseStart_3023857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024009 : List Nat := [1, 2, 1, 1, 4, 5, 8]
def baseStart_3024009 : Nat := 118140960795 + 3024009 * 2 ^ 59
def prefixEnd_3024009 : Nat := 4983230072969 + 3 ^ 40 * 3024009 * 2
def baseEnd_3024009 : Nat := 38340002975855908261243

theorem tailTrace_3024009 : CollatzResearch.WordTrace tailWord_3024009 prefixEnd_3024009 38340002975855908261243 := by
  unfold tailWord_3024009
  simp only [CollatzResearch.WordTrace]
  refine ⟨110294669301539327464859081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73529779534359551643239387 110294669301539327464859081)
  ·
    refine ⟨82721001976154495598644311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110294669301539327464859081 82721001976154495598644311)
    ·
      refine ⟨124081502964231743397966467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82721001976154495598644311 124081502964231743397966467)
      ·
        refine ⟨186122254446347615096949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124081502964231743397966467 186122254446347615096949701)
        ·
          refine ⟨34897922708690177830678069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186122254446347615096949701 34897922708690177830678069)
          ·
            refine ⟨3271680253939704171626069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34897922708690177830678069 3271680253939704171626069)
            ·
              refine ⟨38340002975855908261243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3271680253939704171626069 38340002975855908261243)
              ·
                rfl

theorem cell22_3024009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 8].length) (baseStart_3024009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024009 prefixEnd_3024009 := by exact prefixLift 3024009
  have htrace : WordTrace (prefixWord ++ tailWord_3024009) baseStart_3024009 baseEnd_3024009 := by
    simpa [prefixWord, tailWord_3024009, baseEnd_3024009] using wordTrace_append hprefix tailTrace_3024009
  have hstable : (prefixWord ++ tailWord_3024009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024009).length < 2 ^ (prefixWord ++ tailWord_3024009).sum := by decide
  have hdescent : baseEnd_3024009 < baseStart_3024009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024026 : List Nat := [3, 1, 1, 5, 1, 2, 2, 7]
def baseStart_3024026 : Nat := 118140960795 + 3024026 * 2 ^ 59
def prefixEnd_3024026 : Nat := 4983230072969 + 3 ^ 40 * 3024026 * 2
def baseEnd_3024026 : Nat := 115020655532836349486501

theorem tailTrace_3024026 : CollatzResearch.WordTrace tailWord_3024026 prefixEnd_3024026 115020655532836349486501 := by
  unfold tailWord_3024026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573822335619434842056983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73530192894985159578818621 27573822335619434842056983)
  ·
    refine ⟨41360733503429152263085475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27573822335619434842056983 41360733503429152263085475)
    ·
      refine ⟨62041100255143728394628213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41360733503429152263085475 62041100255143728394628213)
      ·
        refine ⟨5816353148919724536996395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62041100255143728394628213 5816353148919724536996395)
        ·
          refine ⟨8724529723379586805494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816353148919724536996395 8724529723379586805494593)
          ·
            refine ⟨6543397292534690104120945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8724529723379586805494593 6543397292534690104120945)
            ·
              refine ⟨4907547969401017578090709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6543397292534690104120945 4907547969401017578090709)
              ·
                refine ⟨115020655532836349486501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4907547969401017578090709 115020655532836349486501)
                ·
                  rfl

theorem cell22_3024026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_3024026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024026 prefixEnd_3024026 := by exact prefixLift 3024026
  have htrace : WordTrace (prefixWord ++ tailWord_3024026) baseStart_3024026 baseEnd_3024026 := by
    simpa [prefixWord, tailWord_3024026, baseEnd_3024026] using wordTrace_append hprefix tailTrace_3024026
  have hstable : (prefixWord ++ tailWord_3024026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024026).length < 2 ^ (prefixWord ++ tailWord_3024026).sum := by decide
  have hdescent : baseEnd_3024026 < baseStart_3024026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024030 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3024030 : Nat := 118140960795 + 3024030 * 2 ^ 59
def prefixEnd_3024030 : Nat := 4983230072969 + 3 ^ 40 * 3024030 * 2
def baseEnd_3024030 : Nat := 1035187269077272468278497

theorem tailTrace_3024030 : CollatzResearch.WordTrace tailWord_3024030 prefixEnd_3024030 1035187269077272468278497 := by
  unfold tailWord_3024030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786929404307906006421693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73530290156308832034249029 13786929404307906006421693)
  ·
    refine ⟨5170098526615464752408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13786929404307906006421693 5170098526615464752408135)
    ·
      refine ⟨7755147789923197128612203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170098526615464752408135 7755147789923197128612203)
      ·
        refine ⟨11632721684884795692918305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755147789923197128612203 11632721684884795692918305)
        ·
          refine ⟨8724541263663596769688729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11632721684884795692918305 8724541263663596769688729)
          ·
            refine ⟨6543405947747697577266547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8724541263663596769688729 6543405947747697577266547)
            ·
              refine ⟨9815108921621546365899821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543405947747697577266547 9815108921621546365899821)
              ·
                refine ⟨3680665845608079887212433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9815108921621546365899821 3680665845608079887212433)
                ·
                  refine ⟨2760499384206059915409325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680665845608079887212433 2760499384206059915409325)
                  ·
                    refine ⟨1035187269077272468278497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760499384206059915409325 1035187269077272468278497)
                    ·
                      rfl

theorem cell22_3024030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3024030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024030 prefixEnd_3024030 := by exact prefixLift 3024030
  have htrace : WordTrace (prefixWord ++ tailWord_3024030) baseStart_3024030 baseEnd_3024030 := by
    simpa [prefixWord, tailWord_3024030, baseEnd_3024030] using wordTrace_append hprefix tailTrace_3024030
  have hstable : (prefixWord ++ tailWord_3024030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024030).length < 2 ^ (prefixWord ++ tailWord_3024030).sum := by decide
  have hdescent : baseEnd_3024030 < baseStart_3024030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024058 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_3024058 : Nat := 118140960795 + 3024058 * 2 ^ 59
def prefixEnd_3024058 : Nat := 4983230072969 + 3 ^ 40 * 3024058 * 2
def baseEnd_3024058 : Nat := 1035196854049489728578411

theorem tailTrace_3024058 : CollatzResearch.WordTrace tailWord_3024058 prefixEnd_3024058 1035196854049489728578411 := by
  unfold tailWord_3024058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574114119590452208348207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73530970985574539222261885 27574114119590452208348207)
  ·
    refine ⟨41361171179385678312522311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27574114119590452208348207 41361171179385678312522311)
    ·
      refine ⟨62041756769078517468783467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41361171179385678312522311 62041756769078517468783467)
      ·
        refine ⟨93062635153617776203175201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62041756769078517468783467 93062635153617776203175201)
        ·
          refine ⟨69796976365213332152381401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93062635153617776203175201 69796976365213332152381401)
          ·
            refine ⟨52347732273909999114286051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69796976365213332152381401 52347732273909999114286051)
            ·
              refine ⟨78521598410864998671429077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52347732273909999114286051 78521598410864998671429077)
              ·
                refine ⟨1840349962754648406361619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78521598410864998671429077 1840349962754648406361619)
                ·
                  refine ⟨2760524944131972609542429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840349962754648406361619 2760524944131972609542429)
                  ·
                    refine ⟨1035196854049489728578411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760524944131972609542429 1035196854049489728578411)
                    ·
                      rfl

theorem cell22_3024058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_3024058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024058 prefixEnd_3024058 := by exact prefixLift 3024058
  have htrace : WordTrace (prefixWord ++ tailWord_3024058) baseStart_3024058 baseEnd_3024058 := by
    simpa [prefixWord, tailWord_3024058, baseEnd_3024058] using wordTrace_append hprefix tailTrace_3024058
  have hstable : (prefixWord ++ tailWord_3024058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024058).length < 2 ^ (prefixWord ++ tailWord_3024058).sum := by decide
  have hdescent : baseEnd_3024058 < baseStart_3024058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024066 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3024066 : Nat := 118140960795 + 3024066 * 2 ^ 59
def prefixEnd_3024066 : Nat := 4983230072969 + 3 ^ 40 * 3024066 * 2
def baseEnd_3024066 : Nat := 345066530870993458126129

theorem tailTrace_3024066 : CollatzResearch.WordTrace tailWord_3024066 prefixEnd_3024066 345066530870993458126129 := by
  unfold tailWord_3024066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574187065583206549921013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73531165508221884133122701 27574187065583206549921013)
  ·
    refine ⟨2585080037398425614055095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27574187065583206549921013 2585080037398425614055095)
    ·
      refine ⟨3877620056097638421082643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585080037398425614055095 3877620056097638421082643)
      ·
        refine ⟨5816430084146457631623965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877620056097638421082643 5816430084146457631623965)
        ·
          refine ⟨2181161281554921611858987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5816430084146457631623965 2181161281554921611858987)
          ·
            refine ⟨3271741922332382417788481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181161281554921611858987 3271741922332382417788481)
            ·
              refine ⟨2453806441749286813341361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271741922332382417788481 2453806441749286813341361)
              ·
                refine ⟨1840354831311965110006021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453806441749286813341361 1840354831311965110006021)
                ·
                  refine ⟨345066530870993458126129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840354831311965110006021 345066530870993458126129)
                  ·
                    rfl

theorem cell22_3024066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3024066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024066 prefixEnd_3024066 := by exact prefixLift 3024066
  have htrace : WordTrace (prefixWord ++ tailWord_3024066) baseStart_3024066 baseEnd_3024066 := by
    simpa [prefixWord, tailWord_3024066, baseEnd_3024066] using wordTrace_append hprefix tailTrace_3024066
  have hstable : (prefixWord ++ tailWord_3024066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024066).length < 2 ^ (prefixWord ++ tailWord_3024066).sum := by decide
  have hdescent : baseEnd_3024066 < baseStart_3024066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024069 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_3024069 : Nat := 118140960795 + 3024069 * 2 ^ 59
def prefixEnd_3024069 : Nat := 4983230072969 + 3 ^ 40 * 3024069 * 2
def baseEnd_3024069 : Nat := 1035200619574289366553377

theorem tailTrace_3024069 : CollatzResearch.WordTrace tailWord_3024069 prefixEnd_3024069 1035200619574289366553377 := by
  unfold tailWord_3024069
  simp only [CollatzResearch.WordTrace]
  refine ⟨110296857681321957712043261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73531238454214638474695507 110296857681321957712043261)
  ·
    refine ⟨41361321630495734142016223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110296857681321957712043261 41361321630495734142016223)
    ·
      refine ⟨62041982445743601213024335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41361321630495734142016223 62041982445743601213024335)
      ·
        refine ⟨93062973668615401819536503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62041982445743601213024335 93062973668615401819536503)
        ·
          refine ⟨139594460502923102729304755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93062973668615401819536503 139594460502923102729304755)
          ·
            refine ⟨209391690754384654093957133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139594460502923102729304755 209391690754384654093957133)
            ·
              refine ⟨78521884032894245285233925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209391690754384654093957133 78521884032894245285233925)
              ·
                refine ⟨14722853256167670990981361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78521884032894245285233925 14722853256167670990981361)
                ·
                  refine ⟨11042139942125753243236021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14722853256167670990981361 11042139942125753243236021)
                  ·
                    refine ⟨1035200619574289366553377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11042139942125753243236021 1035200619574289366553377)
                    ·
                      rfl

theorem cell22_3024069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_3024069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024069 prefixEnd_3024069 := by exact prefixLift 3024069
  have htrace : WordTrace (prefixWord ++ tailWord_3024069) baseStart_3024069 baseEnd_3024069 := by
    simpa [prefixWord, tailWord_3024069, baseEnd_3024069] using wordTrace_append hprefix tailTrace_3024069
  have hstable : (prefixWord ++ tailWord_3024069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024069).length < 2 ^ (prefixWord ++ tailWord_3024069).sum := by decide
  have hdescent : baseEnd_3024069 < baseStart_3024069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024077 : List Nat := [1, 6, 2, 2, 2, 1, 1, 7]
def baseStart_3024077 : Nat := 118140960795 + 3024077 * 2 ^ 59
def prefixEnd_3024077 : Nat := 4983230072969 + 3 ^ 40 * 3024077 * 2
def baseEnd_3024077 : Nat := 115022595348642223594817

theorem tailTrace_3024077 : CollatzResearch.WordTrace tailWord_3024077 prefixEnd_3024077 115022595348642223594817 := by
  unfold tailWord_3024077
  simp only [CollatzResearch.WordTrace]
  refine ⟨110297149465292975078334485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73531432976861983385556323 110297149465292975078334485)
  ·
    refine ⟨5170178881185608206796929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110297149465292975078334485 5170178881185608206796929)
    ·
      refine ⟨3877634160889206155097697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170178881185608206796929 3877634160889206155097697)
      ·
        refine ⟨2908225620666904616323273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3877634160889206155097697 2908225620666904616323273)
        ·
          refine ⟨2181169215500178462242455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908225620666904616323273 2181169215500178462242455)
          ·
            refine ⟨3271753823250267693363683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181169215500178462242455 3271753823250267693363683)
            ·
              refine ⟨4907630734875401540045525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271753823250267693363683 4907630734875401540045525)
              ·
                refine ⟨115022595348642223594817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4907630734875401540045525 115022595348642223594817)
                ·
                  rfl

theorem cell22_3024077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 7].length) (baseStart_3024077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024077 prefixEnd_3024077 := by exact prefixLift 3024077
  have htrace : WordTrace (prefixWord ++ tailWord_3024077) baseStart_3024077 baseEnd_3024077 := by
    simpa [prefixWord, tailWord_3024077, baseEnd_3024077] using wordTrace_append hprefix tailTrace_3024077
  have hstable : (prefixWord ++ tailWord_3024077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024077).length < 2 ^ (prefixWord ++ tailWord_3024077).sum := by decide
  have hdescent : baseEnd_3024077 < baseStart_3024077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024251 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 6]
def baseStart_3024251 : Nat := 118140960795 + 3024251 * 2 ^ 59
def prefixEnd_3024251 : Nat := 4983230072969 + 3 ^ 40 * 3024251 * 2
def baseEnd_3024251 : Nat := 345087640631233852834273

theorem tailTrace_3024251 : CollatzResearch.WordTrace tailWord_3024251 prefixEnd_3024251 345087640631233852834273 := by
  unfold tailWord_3024251
  simp only [CollatzResearch.WordTrace]
  refine ⟨110303495766662602795168607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73535663844441735196779071 110303495766662602795168607)
  ·
    refine ⟨165455243649993904192752911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110303495766662602795168607 165455243649993904192752911)
    ·
      refine ⟨248182865474990856289129367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165455243649993904192752911 248182865474990856289129367)
      ·
        refine ⟨372274298212486284433694051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248182865474990856289129367 372274298212486284433694051)
        ·
          refine ⟨558411447318729426650541077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372274298212486284433694051 558411447318729426650541077)
          ·
            refine ⟨26175536593065441874244113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 558411447318729426650541077 26175536593065441874244113)
            ·
              refine ⟨19631652444799081405683085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26175536593065441874244113 19631652444799081405683085)
              ·
                refine ⟨7361869666799655527131157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19631652444799081405683085 7361869666799655527131157)
                ·
                  refine ⟨345087640631233852834273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7361869666799655527131157 345087640631233852834273)
                  ·
                    rfl

theorem cell22_3024251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_3024251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024251 prefixEnd_3024251 := by exact prefixLift 3024251
  have htrace : WordTrace (prefixWord ++ tailWord_3024251) baseStart_3024251 baseEnd_3024251 := by
    simpa [prefixWord, tailWord_3024251, baseEnd_3024251] using wordTrace_append hprefix tailTrace_3024251
  have hstable : (prefixWord ++ tailWord_3024251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024251).length < 2 ^ (prefixWord ++ tailWord_3024251).sum := by decide
  have hdescent : baseEnd_3024251 < baseStart_3024251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024285 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3024285 : Nat := 118140960795 + 3024285 * 2 ^ 59
def prefixEnd_3024285 : Nat := 4983230072969 + 3 ^ 40 * 3024285 * 2
def baseEnd_3024285 : Nat := 345091520262845601050905

theorem tailTrace_3024285 : CollatzResearch.WordTrace tailWord_3024285 prefixEnd_3024285 345091520262845601050905 := by
  unfold tailWord_3024285
  simp only [CollatzResearch.WordTrace]
  refine ⟨110304735848539426601906309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73536490565692951067937539 110304735848539426601906309)
  ·
    refine ⟨20682137971601142487857433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110304735848539426601906309 20682137971601142487857433)
    ·
      refine ⟨15511603478700856865893075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20682137971601142487857433 15511603478700856865893075)
      ·
        refine ⟨23267405218051285298839613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15511603478700856865893075 23267405218051285298839613)
        ·
          refine ⟨8725276956769231987064855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23267405218051285298839613 8725276956769231987064855)
          ·
            refine ⟨13087915435153847980597283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725276956769231987064855 13087915435153847980597283)
            ·
              refine ⟨19631873152730771970895925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087915435153847980597283 19631873152730771970895925)
              ·
                refine ⟨1840488108068509872271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19631873152730771970895925 1840488108068509872271493)
                ·
                  refine ⟨345091520262845601050905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840488108068509872271493 345091520262845601050905)
                  ·
                    rfl

theorem cell22_3024285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3024285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024285 prefixEnd_3024285 := by exact prefixLift 3024285
  have htrace : WordTrace (prefixWord ++ tailWord_3024285) baseStart_3024285 baseEnd_3024285 := by
    simpa [prefixWord, tailWord_3024285, baseEnd_3024285] using wordTrace_append hprefix tailTrace_3024285
  have hstable : (prefixWord ++ tailWord_3024285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024285).length < 2 ^ (prefixWord ++ tailWord_3024285).sum := by decide
  have hdescent : baseEnd_3024285 < baseStart_3024285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024287 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 1, 4]
def baseStart_3024287 : Nat := 118140960795 + 3024287 * 2 ^ 59
def prefixEnd_3024287 : Nat := 4983230072969 + 3 ^ 40 * 3024287 * 2
def baseEnd_3024287 : Nat := 1035275245429409464602709

theorem tailTrace_3024287 : CollatzResearch.WordTrace tailWord_3024287 prefixEnd_3024287 1035275245429409464602709 := by
  unfold tailWord_3024287
  simp only [CollatzResearch.WordTrace]
  refine ⟨110304808794532180943479115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73536539196354787295652743 110304808794532180943479115)
  ·
    refine ⟨165457213191798271415218673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110304808794532180943479115 165457213191798271415218673)
    ·
      refine ⟨124092909893848703561414005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165457213191798271415218673 124092909893848703561414005)
      ·
        refine ⟨11633710302548315958882563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124092909893848703561414005 11633710302548315958882563)
        ·
          refine ⟨17450565453822473938323845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633710302548315958882563 17450565453822473938323845)
          ·
            refine ⟨3271981022591713863435721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17450565453822473938323845 3271981022591713863435721)
            ·
              refine ⟨2453985766943785397576791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271981022591713863435721 2453985766943785397576791)
              ·
                refine ⟨3680978650415678096365187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453985766943785397576791 3680978650415678096365187)
                ·
                  refine ⟨5521467975623517144547781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680978650415678096365187 5521467975623517144547781)
                  ·
                    refine ⟨1035275245429409464602709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521467975623517144547781 1035275245429409464602709)
                    ·
                      rfl

theorem cell22_3024287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_3024287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024287 prefixEnd_3024287 := by exact prefixLift 3024287
  have htrace : WordTrace (prefixWord ++ tailWord_3024287) baseStart_3024287 baseEnd_3024287 := by
    simpa [prefixWord, tailWord_3024287, baseEnd_3024287] using wordTrace_append hprefix tailTrace_3024287
  have hstable : (prefixWord ++ tailWord_3024287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024287).length < 2 ^ (prefixWord ++ tailWord_3024287).sum := by decide
  have hdescent : baseEnd_3024287 < baseStart_3024287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024300 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_3024300 : Nat := 118140960795 + 3024300 * 2 ^ 59
def prefixEnd_3024300 : Nat := 4983230072969 + 3 ^ 40 * 3024300 * 2
def baseEnd_3024300 : Nat := 1035279695595081764027669

theorem tailTrace_3024300 : CollatzResearch.WordTrace tailWord_3024300 prefixEnd_3024300 1035279695595081764027669 := by
  unfold tailWord_3024300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55152641471742542081851177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73536855295656722775801569 55152641471742542081851177)
  ·
    refine ⟨41364481103806906561388383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55152641471742542081851177 41364481103806906561388383)
    ·
      refine ⟨62046721655710359842082575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41364481103806906561388383 62046721655710359842082575)
      ·
        refine ⟨93070082483565539763123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62046721655710359842082575 93070082483565539763123863)
        ·
          refine ⟨139605123725348309644685795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93070082483565539763123863 139605123725348309644685795)
          ·
            refine ⟨209407685588022464467028693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139605123725348309644685795 209407685588022464467028693)
            ·
              refine ⟨4907992630969276510945985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209407685588022464467028693 4907992630969276510945985)
              ·
                refine ⟨3680994473226957383209489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907992630969276510945985 3680994473226957383209489)
                ·
                  refine ⟨2760745854920218037407117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680994473226957383209489 2760745854920218037407117)
                  ·
                    refine ⟨1035279695595081764027669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760745854920218037407117 1035279695595081764027669)
                    ·
                      rfl

theorem cell22_3024300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_3024300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024300 prefixEnd_3024300 := by exact prefixLift 3024300
  have htrace : WordTrace (prefixWord ++ tailWord_3024300) baseStart_3024300 baseEnd_3024300 := by
    simpa [prefixWord, tailWord_3024300, baseEnd_3024300] using wordTrace_append hprefix tailTrace_3024300
  have hstable : (prefixWord ++ tailWord_3024300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024300).length < 2 ^ (prefixWord ++ tailWord_3024300).sum := by decide
  have hdescent : baseEnd_3024300 < baseStart_3024300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024317 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_3024317 : Nat := 118140960795 + 3024317 * 2 ^ 59
def prefixEnd_3024317 : Nat := 4983230072969 + 3 ^ 40 * 3024317 * 2
def baseEnd_3024317 : Nat := 1035285515042499386352617

theorem tailTrace_3024317 : CollatzResearch.WordTrace tailWord_3024317 prefixEnd_3024317 1035285515042499386352617 := by
  unfold tailWord_3024317
  simp only [CollatzResearch.WordTrace]
  refine ⟨110305902984423496067071205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73537268656282330711380803 110305902984423496067071205)
  ·
    refine ⟨20682356809579405512575851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110305902984423496067071205 20682356809579405512575851)
    ·
      refine ⟨31023535214369108268863777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20682356809579405512575851 31023535214369108268863777)
      ·
        refine ⟨23267651410776831201647833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31023535214369108268863777 23267651410776831201647833)
        ·
          refine ⟨17450738558082623401235875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23267651410776831201647833 17450738558082623401235875)
          ·
            refine ⟨26176107837123935101853813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17450738558082623401235875 26176107837123935101853813)
            ·
              refine ⟨2454010109730368915798795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26176107837123935101853813 2454010109730368915798795)
              ·
                refine ⟨3681015164595553373698193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454010109730368915798795 3681015164595553373698193)
                ·
                  refine ⟨2760761373446665030273645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681015164595553373698193 2760761373446665030273645)
                  ·
                    refine ⟨1035285515042499386352617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2760761373446665030273645 1035285515042499386352617)
                    ·
                      rfl

theorem cell22_3024317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_3024317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024317 prefixEnd_3024317 := by exact prefixLift 3024317
  have htrace : WordTrace (prefixWord ++ tailWord_3024317) baseStart_3024317 baseEnd_3024317 := by
    simpa [prefixWord, tailWord_3024317, baseEnd_3024317] using wordTrace_append hprefix tailTrace_3024317
  have hstable : (prefixWord ++ tailWord_3024317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024317).length < 2 ^ (prefixWord ++ tailWord_3024317).sum := by decide
  have hdescent : baseEnd_3024317 < baseStart_3024317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024330 : List Nat := [3, 1, 2, 1, 2, 5, 2, 6]
def baseStart_3024330 : Nat := 118140960795 + 3024330 * 2 ^ 59
def prefixEnd_3024330 : Nat := 4983230072969 + 3 ^ 40 * 3024330 * 2
def baseEnd_3024330 : Nat := 115032218356463520641953

theorem tailTrace_3024330 : CollatzResearch.WordTrace tailWord_3024330 prefixEnd_3024330 115032218356463520641953 := by
  unfold tailWord_3024330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27576594283344099821823611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73537584755584266191529629 27576594283344099821823611)
  ·
    refine ⟨41364891425016149732735417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27576594283344099821823611 41364891425016149732735417)
    ·
      refine ⟨31023668568762112299551563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41364891425016149732735417 31023668568762112299551563)
      ·
        refine ⟨46535502853143168449327345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31023668568762112299551563 46535502853143168449327345)
        ·
          refine ⟨34901627139857376336995509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46535502853143168449327345 34901627139857376336995509)
          ·
            refine ⟨3272027544361629031593329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34901627139857376336995509 3272027544361629031593329)
            ·
              refine ⟨2454020658271221773694997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272027544361629031593329 2454020658271221773694997)
              ·
                refine ⟨115032218356463520641953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2454020658271221773694997 115032218356463520641953)
                ·
                  rfl

theorem cell22_3024330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_3024330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024330 prefixEnd_3024330 := by exact prefixLift 3024330
  have htrace : WordTrace (prefixWord ++ tailWord_3024330) baseStart_3024330 baseEnd_3024330 := by
    simpa [prefixWord, tailWord_3024330, baseEnd_3024330] using wordTrace_append hprefix tailTrace_3024330
  have hstable : (prefixWord ++ tailWord_3024330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024330).length < 2 ^ (prefixWord ++ tailWord_3024330).sum := by decide
  have hdescent : baseEnd_3024330 < baseStart_3024330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024433 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3024433 : Nat := 118140960795 + 3024433 * 2 ^ 59
def prefixEnd_3024433 : Nat := 4983230072969 + 3 ^ 40 * 3024433 * 2
def baseEnd_3024433 : Nat := 1035325224213113750452261

theorem tailTrace_3024433 : CollatzResearch.WordTrace tailWord_3024433 prefixEnd_3024433 1035325224213113750452261 := by
  unfold tailWord_3024433
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310133852003247878293953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73540089234668831918862635 110310133852003247878293953)
  ·
    refine ⟨82732600389002435908720465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110310133852003247878293953 82732600389002435908720465)
    ·
      refine ⟨62049450291751826931540349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82732600389002435908720465 62049450291751826931540349)
      ·
        refine ⟨23268543859406935099327631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62049450291751826931540349 23268543859406935099327631)
        ·
          refine ⟨34902815789110402648991447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23268543859406935099327631 34902815789110402648991447)
          ·
            refine ⟨52354223683665603973487171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34902815789110402648991447 52354223683665603973487171)
            ·
              refine ⟨78531335525498405960230757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52354223683665603973487171 78531335525498405960230757)
              ·
                refine ⟨14724625411030951117543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78531335525498405960230757 14724625411030951117543267)
                ·
                  refine ⟨22086938116546426676314901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14724625411030951117543267 22086938116546426676314901)
                  ·
                    refine ⟨1035325224213113750452261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22086938116546426676314901 1035325224213113750452261)
                    ·
                      rfl

theorem cell22_3024433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3024433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024433 prefixEnd_3024433 := by exact prefixLift 3024433
  have htrace : WordTrace (prefixWord ++ tailWord_3024433) baseStart_3024433 baseEnd_3024433 := by
    simpa [prefixWord, tailWord_3024433, baseEnd_3024433] using wordTrace_append hprefix tailTrace_3024433
  have hstable : (prefixWord ++ tailWord_3024433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024433).length < 2 ^ (prefixWord ++ tailWord_3024433).sum := by decide
  have hdescent : baseEnd_3024433 < baseStart_3024433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024435 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_3024435 : Nat := 118140960795 + 3024435 * 2 ^ 59
def prefixEnd_3024435 : Nat := 4983230072969 + 3 ^ 40 * 3024435 * 2
def baseEnd_3024435 : Nat := 1035325908853986411902255

theorem tailTrace_3024435 : CollatzResearch.WordTrace tailWord_3024435 prefixEnd_3024435 1035325908853986411902255 := by
  unfold tailWord_3024435
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310206797996002219866759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73540137865330668146577839 110310206797996002219866759)
  ·
    refine ⟨165465310196994003329800139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110310206797996002219866759 165465310196994003329800139)
    ·
      refine ⟨248197965295491004994700209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165465310196994003329800139 248197965295491004994700209)
      ·
        refine ⟨186148473971618253746025157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248197965295491004994700209 186148473971618253746025157)
        ·
          refine ⟨34902838869678422577379717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186148473971618253746025157 34902838869678422577379717)
          ·
            refine ⟨6544282288064704233258697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34902838869678422577379717 6544282288064704233258697)
            ·
              refine ⟨4908211716048528174944023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544282288064704233258697 4908211716048528174944023)
              ·
                refine ⟨7362317574072792262416035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908211716048528174944023 7362317574072792262416035)
                ·
                  refine ⟨11043476361109188393624053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362317574072792262416035 11043476361109188393624053)
                  ·
                    refine ⟨1035325908853986411902255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11043476361109188393624053 1035325908853986411902255)
                    ·
                      rfl

theorem cell22_3024435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_3024435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024435 prefixEnd_3024435 := by exact prefixLift 3024435
  have htrace : WordTrace (prefixWord ++ tailWord_3024435) baseStart_3024435 baseEnd_3024435 := by
    simpa [prefixWord, tailWord_3024435, baseEnd_3024435] using wordTrace_append hprefix tailTrace_3024435
  have hstable : (prefixWord ++ tailWord_3024435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024435).length < 2 ^ (prefixWord ++ tailWord_3024435).sum := by decide
  have hdescent : baseEnd_3024435 < baseStart_3024435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024544 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_3024544 : Nat := 118140960795 + 3024544 * 2 ^ 59
def prefixEnd_3024544 : Nat := 4983230072969 + 3 ^ 40 * 3024544 * 2
def baseEnd_3024544 : Nat := 345121073927182153642307

theorem tailTrace_3024544 : CollatzResearch.WordTrace tailWord_3024544 prefixEnd_3024544 345121073927182153642307 := by
  unfold tailWord_3024544
  simp only [CollatzResearch.WordTrace]
  refine ⟨55157091177300556917792343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73542788236400742557056457 55157091177300556917792343)
  ·
    refine ⟨82735636765950835376688515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55157091177300556917792343 82735636765950835376688515)
    ·
      refine ⟨124103455148926253065032773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82735636765950835376688515 124103455148926253065032773)
      ·
        refine ⟨23269397840423672449693645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124103455148926253065032773 23269397840423672449693645)
        ·
          refine ⟨8726024190158877168635117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23269397840423672449693645 8726024190158877168635117)
          ·
            refine ⟨3272259071309578938238169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8726024190158877168635117 3272259071309578938238169)
            ·
              refine ⟨2454194303482184203678627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272259071309578938238169 2454194303482184203678627)
              ·
                refine ⟨3681291455223276305517941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454194303482184203678627 3681291455223276305517941)
                ·
                  refine ⟨345121073927182153642307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3681291455223276305517941 345121073927182153642307)
                  ·
                    rfl

theorem cell22_3024544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_3024544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024544 prefixEnd_3024544 := by exact prefixLift 3024544
  have htrace : WordTrace (prefixWord ++ tailWord_3024544) baseStart_3024544 baseEnd_3024544 := by
    simpa [prefixWord, tailWord_3024544, baseEnd_3024544] using wordTrace_append hprefix tailTrace_3024544
  have hstable : (prefixWord ++ tailWord_3024544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024544).length < 2 ^ (prefixWord ++ tailWord_3024544).sum := by decide
  have hdescent : baseEnd_3024544 < baseStart_3024544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024557 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3024557 : Nat := 118140960795 + 3024557 * 2 ^ 59
def prefixEnd_3024557 : Nat := 4983230072969 + 3 ^ 40 * 3024557 * 2
def baseEnd_3024557 : Nat := 1035367671947218760351881

theorem tailTrace_3024557 : CollatzResearch.WordTrace tailWord_3024557 prefixEnd_3024557 1035367671947218760351881 := by
  unfold tailWord_3024557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110314656503554017055807925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73543104335702678037205283 110314656503554017055807925)
  ·
    refine ⟨10341999047208189098981993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110314656503554017055807925 10341999047208189098981993)
    ·
      refine ⟨7756499285406141824236495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10341999047208189098981993 7756499285406141824236495)
      ·
        refine ⟨11634748928109212736354743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756499285406141824236495 11634748928109212736354743)
        ·
          refine ⟨17452123392163819104532115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11634748928109212736354743 17452123392163819104532115)
          ·
            refine ⟨26178185088245728656798173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17452123392163819104532115 26178185088245728656798173)
            ·
              refine ⟨9816819408092148246299315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26178185088245728656798173 9816819408092148246299315)
              ·
                refine ⟨14725229112138222369448973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816819408092148246299315 14725229112138222369448973)
                ·
                  refine ⟨5521960917051833388543365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14725229112138222369448973 5521960917051833388543365)
                  ·
                    refine ⟨1035367671947218760351881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521960917051833388543365 1035367671947218760351881)
                    ·
                      rfl

theorem cell22_3024557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3024557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024557 prefixEnd_3024557 := by exact prefixLift 3024557
  have htrace : WordTrace (prefixWord ++ tailWord_3024557) baseStart_3024557 baseEnd_3024557 := by
    simpa [prefixWord, tailWord_3024557, baseEnd_3024557] using wordTrace_append hprefix tailTrace_3024557
  have hstable : (prefixWord ++ tailWord_3024557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024557).length < 2 ^ (prefixWord ++ tailWord_3024557).sum := by decide
  have hdescent : baseEnd_3024557 < baseStart_3024557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024570 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_3024570 : Nat := 118140960795 + 3024570 * 2 ^ 59
def prefixEnd_3024570 : Nat := 4983230072969 + 3 ^ 40 * 3024570 * 2
def baseEnd_3024570 : Nat := 1035372122112891059776841

theorem tailTrace_3024570 : CollatzResearch.WordTrace tailWord_3024570 prefixEnd_3024570 1035372122112891059776841 := by
  unfold tailWord_3024570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578782663126730069007791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73543420435004613517354109 27578782663126730069007791)
  ·
    refine ⟨41368173994690095103511687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27578782663126730069007791 41368173994690095103511687)
    ·
      refine ⟨62052260992035142655267531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41368173994690095103511687 62052260992035142655267531)
      ·
        refine ⟨93078391488052713982901297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62052260992035142655267531 93078391488052713982901297)
        ·
          refine ⟨69808793616039535487175973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93078391488052713982901297 69808793616039535487175973)
          ·
            refine ⟨13089148803007412903845495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69808793616039535487175973 13089148803007412903845495)
            ·
              refine ⟨19633723204511119355768243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13089148803007412903845495 19633723204511119355768243)
              ·
                refine ⟨29450584806766679033652365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19633723204511119355768243 29450584806766679033652365)
                ·
                  refine ⟨11043969302537504637619637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29450584806766679033652365 11043969302537504637619637)
                  ·
                    refine ⟨1035372122112891059776841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11043969302537504637619637 1035372122112891059776841)
                    ·
                      rfl

theorem cell22_3024570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_3024570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024570 prefixEnd_3024570 := by exact prefixLift 3024570
  have htrace : WordTrace (prefixWord ++ tailWord_3024570) baseStart_3024570 baseEnd_3024570 := by
    simpa [prefixWord, tailWord_3024570, baseEnd_3024570] using wordTrace_append hprefix tailTrace_3024570
  have hstable : (prefixWord ++ tailWord_3024570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024570).length < 2 ^ (prefixWord ++ tailWord_3024570).sum := by decide
  have hdescent : baseEnd_3024570 < baseStart_3024570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024578 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3024578 : Nat := 118140960795 + 3024578 * 2 ^ 59
def prefixEnd_3024578 : Nat := 4983230072969 + 3 ^ 40 * 3024578 * 2
def baseEnd_3024578 : Nat := 345124953558793901858939

theorem tailTrace_3024578 : CollatzResearch.WordTrace tailWord_3024578 prefixEnd_3024578 345124953558793901858939 := by
  unfold tailWord_3024578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578855609119484410580597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73543614957651958428214925 27578855609119484410580597)
  ·
    refine ⟨2585517713354951663491931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27578855609119484410580597 2585517713354951663491931)
    ·
      refine ⟨3878276570032427495237897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585517713354951663491931 3878276570032427495237897)
      ·
        refine ⟨2908707427524320621428423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3878276570032427495237897 2908707427524320621428423)
        ·
          refine ⟨4363061141286480932142635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908707427524320621428423 4363061141286480932142635)
          ·
            refine ⟨6544591711929721398213953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363061141286480932142635 6544591711929721398213953)
            ·
              refine ⟨4908443783947291048660465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544591711929721398213953 4908443783947291048660465)
              ·
                refine ⟨3681332837960468286495349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908443783947291048660465 3681332837960468286495349)
                ·
                  refine ⟨345124953558793901858939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3681332837960468286495349 345124953558793901858939)
                  ·
                    rfl

theorem cell22_3024578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3024578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024578 prefixEnd_3024578 := by exact prefixLift 3024578
  have htrace : WordTrace (prefixWord ++ tailWord_3024578) baseStart_3024578 baseEnd_3024578 := by
    simpa [prefixWord, tailWord_3024578, baseEnd_3024578] using wordTrace_append hprefix tailTrace_3024578
  have hstable : (prefixWord ++ tailWord_3024578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024578).length < 2 ^ (prefixWord ++ tailWord_3024578).sum := by decide
  have hdescent : baseEnd_3024578 < baseStart_3024578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024582 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3024582 : Nat := 118140960795 + 3024582 * 2 ^ 59
def prefixEnd_3024582 : Nat := 4983230072969 + 3 ^ 40 * 3024582 * 2
def baseEnd_3024582 : Nat := 1035376229958127028476805

theorem tailTrace_3024582 : CollatzResearch.WordTrace tailWord_3024582 prefixEnd_3024582 1035376229958127028476805 := by
  unfold tailWord_3024582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447361510264482697670875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73543712218975630883645333 3447361510264482697670875)
  ·
    refine ⟨5171042265396724046506313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447361510264482697670875 5171042265396724046506313)
    ·
      refine ⟨3878281699047543034879735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5171042265396724046506313 3878281699047543034879735)
      ·
        refine ⟨5817422548571314552319603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878281699047543034879735 5817422548571314552319603)
        ·
          refine ⟨8726133822856971828479405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817422548571314552319603 8726133822856971828479405)
          ·
            refine ⟨3272300183571364435679777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8726133822856971828479405 3272300183571364435679777)
            ·
              refine ⟨2454225137678523326759833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272300183571364435679777 2454225137678523326759833)
              ·
                refine ⟨1840668853258892495069875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454225137678523326759833 1840668853258892495069875)
                ·
                  refine ⟨2761003279888338742604813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840668853258892495069875 2761003279888338742604813)
                  ·
                    refine ⟨1035376229958127028476805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761003279888338742604813 1035376229958127028476805)
                    ·
                      rfl

theorem cell22_3024582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3024582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024582 prefixEnd_3024582 := by exact prefixLift 3024582
  have htrace : WordTrace (prefixWord ++ tailWord_3024582) baseStart_3024582 baseEnd_3024582 := by
    simpa [prefixWord, tailWord_3024582, baseEnd_3024582] using wordTrace_append hprefix tailTrace_3024582
  have hstable : (prefixWord ++ tailWord_3024582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024582).length < 2 ^ (prefixWord ++ tailWord_3024582).sum := by decide
  have hdescent : baseEnd_3024582 < baseStart_3024582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024638 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3024638 : Nat := 118140960795 + 3024638 * 2 ^ 59
def prefixEnd_3024638 : Nat := 4983230072969 + 3 ^ 40 * 3024638 * 2
def baseEnd_3024638 : Nat := 1035395399902561549076633

theorem tailTrace_3024638 : CollatzResearch.WordTrace tailWord_3024638 prefixEnd_3024638 1035395399902561549076633 := by
  unfold tailWord_3024638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789701352032570986188321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73545073877507045259671045 13789701352032570986188321)
  ·
    refine ⟨10342276014024428239641241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13789701352032570986188321 10342276014024428239641241)
    ·
      refine ⟨7756707010518321179730931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10342276014024428239641241 7756707010518321179730931)
      ·
        refine ⟨11635060515777481769596397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756707010518321179730931 11635060515777481769596397)
        ·
          refine ⟨4363147693416555663598649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11635060515777481769596397 4363147693416555663598649)
          ·
            refine ⟨3272360770062416747698987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363147693416555663598649 3272360770062416747698987)
            ·
              refine ⟨4908541155093625121548481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272360770062416747698987 4908541155093625121548481)
              ·
                refine ⟨3681405866320218841161361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908541155093625121548481 3681405866320218841161361)
                ·
                  refine ⟨2761054399740164130871021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681405866320218841161361 2761054399740164130871021)
                  ·
                    refine ⟨1035395399902561549076633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761054399740164130871021 1035395399902561549076633)
                    ·
                      rfl

theorem cell22_3024638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3024638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024638 prefixEnd_3024638 := by exact prefixLift 3024638
  have htrace : WordTrace (prefixWord ++ tailWord_3024638) baseStart_3024638 baseEnd_3024638 := by
    simpa [prefixWord, tailWord_3024638, baseEnd_3024638] using wordTrace_append hprefix tailTrace_3024638
  have hstable : (prefixWord ++ tailWord_3024638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024638).length < 2 ^ (prefixWord ++ tailWord_3024638).sum := by decide
  have hdescent : baseEnd_3024638 < baseStart_3024638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024707 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 6]
def baseStart_3024707 : Nat := 118140960795 + 3024707 * 2 ^ 59
def prefixEnd_3024707 : Nat := 4983230072969 + 3 ^ 40 * 3024707 * 2
def baseEnd_3024707 : Nat := 345139673337556123033807

theorem tailTrace_3024707 : CollatzResearch.WordTrace tailWord_3024707 prefixEnd_3024707 345139673337556123033807 := by
  unfold tailWord_3024707
  simp only [CollatzResearch.WordTrace]
  refine ⟨110320127453010592673768375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73546751635340395115845583 110320127453010592673768375)
  ·
    refine ⟨165480191179515889010652563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110320127453010592673768375 165480191179515889010652563)
    ·
      refine ⟨248220286769273833515978845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165480191179515889010652563 248220286769273833515978845)
      ·
        refine ⟨93082607538477687568492067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248220286769273833515978845 93082607538477687568492067)
        ·
          refine ⟨139623911307716531352738101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93082607538477687568492067 139623911307716531352738101)
          ·
            refine ⟨13089741685098424814319197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139623911307716531352738101 13089741685098424814319197)
            ·
              refine ⟨4908653131911909305369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13089741685098424814319197 4908653131911909305369699)
              ·
                refine ⟨7362979697867863958054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908653131911909305369699 7362979697867863958054549)
                ·
                  refine ⟨345139673337556123033807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7362979697867863958054549 345139673337556123033807)
                  ·
                    rfl

theorem cell22_3024707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_3024707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024707 prefixEnd_3024707 := by exact prefixLift 3024707
  have htrace : WordTrace (prefixWord ++ tailWord_3024707) baseStart_3024707 baseEnd_3024707 := by
    simpa [prefixWord, tailWord_3024707, baseEnd_3024707] using wordTrace_append hprefix tailTrace_3024707
  have hstable : (prefixWord ++ tailWord_3024707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024707).length < 2 ^ (prefixWord ++ tailWord_3024707).sum := by decide
  have hdescent : baseEnd_3024707 < baseStart_3024707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024739 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_3024739 : Nat := 118140960795 + 3024739 * 2 ^ 59
def prefixEnd_3024739 : Nat := 4983230072969 + 3 ^ 40 * 3024739 * 2
def baseEnd_3024739 : Nat := 1035429974266630952301323

theorem tailTrace_3024739 : CollatzResearch.WordTrace tailWord_3024739 prefixEnd_3024739 1035429974266630952301323 := by
  unfold tailWord_3024739
  simp only [CollatzResearch.WordTrace]
  refine ⟨110321294588894662138933271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73547529725929774759288847 110321294588894662138933271)
  ·
    refine ⟨165481941883341993208399907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110321294588894662138933271 165481941883341993208399907)
    ·
      refine ⟨248222912825012989812599861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165481941883341993208399907 248222912825012989812599861)
      ·
        refine ⟨23270898077344967794931237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248222912825012989812599861 23270898077344967794931237)
        ·
          refine ⟨4363293389502181461549607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23270898077344967794931237 4363293389502181461549607)
          ·
            refine ⟨6544940084253272192324411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363293389502181461549607 6544940084253272192324411)
            ·
              refine ⟨9817410126379908288486617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544940084253272192324411 9817410126379908288486617)
              ·
                refine ⟨7363057594784931216364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9817410126379908288486617 7363057594784931216364963)
                ·
                  refine ⟨11044586392177396824547445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363057594784931216364963 11044586392177396824547445)
                  ·
                    refine ⟨1035429974266630952301323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11044586392177396824547445 1035429974266630952301323)
                    ·
                      rfl

theorem cell22_3024739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_3024739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024739 prefixEnd_3024739 := by exact prefixLift 3024739
  have htrace : WordTrace (prefixWord ++ tailWord_3024739) baseStart_3024739 baseEnd_3024739 := by
    simpa [prefixWord, tailWord_3024739, baseEnd_3024739] using wordTrace_append hprefix tailTrace_3024739
  have hstable : (prefixWord ++ tailWord_3024739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024739).length < 2 ^ (prefixWord ++ tailWord_3024739).sum := by decide
  have hdescent : baseEnd_3024739 < baseStart_3024739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024758 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3024758 : Nat := 118140960795 + 3024758 * 2 ^ 59
def prefixEnd_3024758 : Nat := 4983230072969 + 3 ^ 40 * 3024758 * 2
def baseEnd_3024758 : Nat := 345145492784973745358755

theorem tailTrace_3024758 : CollatzResearch.WordTrace tailWord_3024758 prefixEnd_3024758 345145492784973745358755 := by
  unfold tailWord_3024758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895124223489114273992183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73547991717217218922583285 6895124223489114273992183)
  ·
    refine ⟨10342686335233671410988275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6895124223489114273992183 10342686335233671410988275)
    ·
      refine ⟨15514029502850507116482413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342686335233671410988275 15514029502850507116482413)
      ·
        refine ⟨5817761063568940168680905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15514029502850507116482413 5817761063568940168680905)
        ·
          refine ⟨4363320797676705126510679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817761063568940168680905 4363320797676705126510679)
          ·
            refine ⟨6544981196515057689766019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363320797676705126510679 6544981196515057689766019)
            ·
              refine ⟨9817471794772586534649029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544981196515057689766019 9817471794772586534649029)
              ·
                refine ⟨1840775961519859975246693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9817471794772586534649029 1840775961519859975246693)
                ·
                  refine ⟨345145492784973745358755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840775961519859975246693 345145492784973745358755)
                  ·
                    rfl

theorem cell22_3024758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3024758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024758 prefixEnd_3024758 := by exact prefixLift 3024758
  have htrace : WordTrace (prefixWord ++ tailWord_3024758) baseStart_3024758 baseEnd_3024758 := by
    simpa [prefixWord, tailWord_3024758, baseEnd_3024758] using wordTrace_append hprefix tailTrace_3024758
  have hstable : (prefixWord ++ tailWord_3024758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024758).length < 2 ^ (prefixWord ++ tailWord_3024758).sum := by decide
  have hdescent : baseEnd_3024758 < baseStart_3024758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024786 : List Nat := [3, 2, 3, 2, 1, 2, 3, 6]
def baseStart_3024786 : Nat := 118140960795 + 3024786 * 2 ^ 59
def prefixEnd_3024786 : Nat := 4983230072969 + 3 ^ 40 * 3024786 * 2
def baseEnd_3024786 : Nat := 115049562591904277375131

theorem tailTrace_3024786 : CollatzResearch.WordTrace tailWord_3024786 prefixEnd_3024786 115049562591904277375131 := by
  unfold tailWord_3024786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580752204931097291473553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73548672546482926110596141 27580752204931097291473553)
  ·
    refine ⟨20685564153698322968605165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27580752204931097291473553 20685564153698322968605165)
    ·
      refine ⟨7757086557636871113226937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20685564153698322968605165 7757086557636871113226937)
      ·
        refine ⟨5817814918227653334920203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7757086557636871113226937 5817814918227653334920203)
        ·
          refine ⟨8726722377341480002380305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817814918227653334920203 8726722377341480002380305)
          ·
            refine ⟨6545041783006110001785229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8726722377341480002380305 6545041783006110001785229)
            ·
              refine ⟨2454390668627291250669461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6545041783006110001785229 2454390668627291250669461)
              ·
                refine ⟨115049562591904277375131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2454390668627291250669461 115049562591904277375131)
                ·
                  rfl

theorem cell22_3024786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_3024786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024786 prefixEnd_3024786 := by exact prefixLift 3024786
  have htrace : WordTrace (prefixWord ++ tailWord_3024786) baseStart_3024786 baseEnd_3024786 := by
    simpa [prefixWord, tailWord_3024786, baseEnd_3024786] using wordTrace_append hprefix tailTrace_3024786
  have hstable : (prefixWord ++ tailWord_3024786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024786).length < 2 ^ (prefixWord ++ tailWord_3024786).sum := by decide
  have hdescent : baseEnd_3024786 < baseStart_3024786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024829 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3024829 : Nat := 118140960795 + 3024829 * 2 ^ 59
def prefixEnd_3024829 : Nat := 4983230072969 + 3 ^ 40 * 3024829 * 2
def baseEnd_3024829 : Nat := 1035460783105900717551047

theorem tailTrace_3024829 : CollatzResearch.WordTrace tailWord_3024829 prefixEnd_3024829 1035460783105900717551047 := by
  unfold tailWord_3024829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110324577158568607509709541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73549718105712405006473027 110324577158568607509709541)
  ·
    refine ⟨20685858217231613908070539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110324577158568607509709541 20685858217231613908070539)
    ·
      refine ⟨31028787325847420862105809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20685858217231613908070539 31028787325847420862105809)
      ·
        refine ⟨23271590494385565646579357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31028787325847420862105809 23271590494385565646579357)
        ·
          refine ⟨8726846435394587117467259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23271590494385565646579357 8726846435394587117467259)
          ·
            refine ⟨13090269653091880676200889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726846435394587117467259 13090269653091880676200889)
            ·
              refine ⟨9817702239818910507150667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13090269653091880676200889 9817702239818910507150667)
              ·
                refine ⟨14726553359728365760726001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817702239818910507150667 14726553359728365760726001)
                ·
                  refine ⟨11044915019796274320544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14726553359728365760726001 11044915019796274320544501)
                  ·
                    refine ⟨1035460783105900717551047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11044915019796274320544501 1035460783105900717551047)
                    ·
                      rfl

theorem cell22_3024829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3024829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024829 prefixEnd_3024829 := by exact prefixLift 3024829
  have htrace : WordTrace (prefixWord ++ tailWord_3024829) baseStart_3024829 baseEnd_3024829 := by
    simpa [prefixWord, tailWord_3024829, baseEnd_3024829] using wordTrace_append hprefix tailTrace_3024829
  have hstable : (prefixWord ++ tailWord_3024829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024829).length < 2 ^ (prefixWord ++ tailWord_3024829).sum := by decide
  have hdescent : baseEnd_3024829 < baseStart_3024829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024953 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_3024953 : Nat := 118140960795 + 3024953 * 2 ^ 59
def prefixEnd_3024953 : Nat := 4983230072969 + 3 ^ 40 * 3024953 * 2
def baseEnd_3024953 : Nat := 1035503230840005727450667

theorem tailTrace_3024953 : CollatzResearch.WordTrace tailWord_3024953 prefixEnd_3024953 1035503230840005727450667 := by
  unfold tailWord_3024953
  simp only [CollatzResearch.WordTrace]
  refine ⟨110329099810119376687223513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73552733206746251124815675 110329099810119376687223513)
  ·
    refine ⟨82746824857589532515417635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110329099810119376687223513 82746824857589532515417635)
    ·
      refine ⟨124120237286384298773126453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82746824857589532515417635 124120237286384298773126453)
      ·
        refine ⟨11636272245598528009980605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124120237286384298773126453 11636272245598528009980605)
        ·
          refine ⟨4363602092099448003742727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11636272245598528009980605 4363602092099448003742727)
          ·
            refine ⟨6545403138149172005614091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363602092099448003742727 6545403138149172005614091)
            ·
              refine ⟨9818104707223758008421137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545403138149172005614091 9818104707223758008421137)
              ·
                refine ⟨7363578530417818506315853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9818104707223758008421137 7363578530417818506315853)
                ·
                  refine ⟨2761341948906681939868445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7363578530417818506315853 2761341948906681939868445)
                  ·
                    refine ⟨1035503230840005727450667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761341948906681939868445 1035503230840005727450667)
                    ·
                      rfl

theorem cell22_3024953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_3024953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3024953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3024953 prefixEnd_3024953 := by exact prefixLift 3024953
  have htrace : WordTrace (prefixWord ++ tailWord_3024953) baseStart_3024953 baseEnd_3024953 := by
    simpa [prefixWord, tailWord_3024953, baseEnd_3024953] using wordTrace_append hprefix tailTrace_3024953
  have hstable : (prefixWord ++ tailWord_3024953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024953).length < 2 ^ (prefixWord ++ tailWord_3024953).sum := by decide
  have hdescent : baseEnd_3024953 < baseStart_3024953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025056 : List Nat := [2, 1, 1, 4, 2, 3, 2, 7]
def baseStart_3025056 : Nat := 118140960795 + 3025056 * 2 ^ 59
def prefixEnd_3025056 : Nat := 4983230072969 + 3 ^ 40 * 3025056 * 2
def baseEnd_3025056 : Nat := 115059832204994199125039

theorem tailTrace_3025056 : CollatzResearch.WordTrace tailWord_3025056 prefixEnd_3025056 115059832204994199125039 := by
  unfold tailWord_3025056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55166428264373112639111511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73555237685830816852148681 55166428264373112639111511)
  ·
    refine ⟨82749642396559668958667267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55166428264373112639111511 82749642396559668958667267)
    ·
      refine ⟨124124463594839503438000901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82749642396559668958667267 124124463594839503438000901)
      ·
        refine ⟨23273336924032406894625169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124124463594839503438000901 23273336924032406894625169)
        ·
          refine ⟨17455002693024305170968877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23273336924032406894625169 17455002693024305170968877)
          ·
            refine ⟨6545626009884114439113329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17455002693024305170968877 6545626009884114439113329)
            ·
              refine ⟨4909219507413085829334997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6545626009884114439113329 4909219507413085829334997)
              ·
                refine ⟨115059832204994199125039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4909219507413085829334997 115059832204994199125039)
                ·
                  rfl

theorem cell22_3025056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_3025056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025056 prefixEnd_3025056 := by exact prefixLift 3025056
  have htrace : WordTrace (prefixWord ++ tailWord_3025056) baseStart_3025056 baseEnd_3025056 := by
    simpa [prefixWord, tailWord_3025056, baseEnd_3025056] using wordTrace_append hprefix tailTrace_3025056
  have hstable : (prefixWord ++ tailWord_3025056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025056).length < 2 ^ (prefixWord ++ tailWord_3025056).sum := by decide
  have hdescent : baseEnd_3025056 < baseStart_3025056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025060 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3025060 : Nat := 118140960795 + 3025060 * 2 ^ 59
def prefixEnd_3025060 : Nat := 4983230072969 + 3 ^ 40 * 3025060 * 2
def baseEnd_3025060 : Nat := 1035539859126693115025339

theorem tailTrace_3025060 : CollatzResearch.WordTrace tailWord_3025060 prefixEnd_3025060 1035539859126693115025339 := by
  unfold tailWord_3025060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55166501210365866980684317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73555334947154489307579089 55166501210365866980684317)
  ·
    refine ⟨20687437953887200117756619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55166501210365866980684317 20687437953887200117756619)
    ·
      refine ⟨31031156930830800176634929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20687437953887200117756619 31031156930830800176634929)
      ·
        refine ⟨23273367698123100132476197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31031156930830800176634929 23273367698123100132476197)
        ·
          refine ⟨4363756443398081274839287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23273367698123100132476197 4363756443398081274839287)
          ·
            refine ⟨6545634665097121912258931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363756443398081274839287 6545634665097121912258931)
            ·
              refine ⟨9818451997645682868388397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545634665097121912258931 9818451997645682868388397)
              ·
                refine ⟨3681919499117131075645649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9818451997645682868388397 3681919499117131075645649)
                ·
                  refine ⟨2761439624337848306734237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681919499117131075645649 2761439624337848306734237)
                  ·
                    refine ⟨1035539859126693115025339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761439624337848306734237 1035539859126693115025339)
                    ·
                      rfl

theorem cell22_3025060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3025060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025060 prefixEnd_3025060 := by exact prefixLift 3025060
  have htrace : WordTrace (prefixWord ++ tailWord_3025060) baseStart_3025060 baseEnd_3025060 := by
    simpa [prefixWord, tailWord_3025060, baseEnd_3025060] using wordTrace_append hprefix tailTrace_3025060
  have hstable : (prefixWord ++ tailWord_3025060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025060).length < 2 ^ (prefixWord ++ tailWord_3025060).sum := by decide
  have hdescent : baseEnd_3025060 < baseStart_3025060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025071 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 5, 3]
def baseStart_3025071 : Nat := 118140960795 + 3025071 * 2 ^ 59
def prefixEnd_3025071 : Nat := 4983230072969 + 3 ^ 40 * 3025071 * 2
def baseEnd_3025071 : Nat := 1035543624651492753000305

theorem tailTrace_3025071 : CollatzResearch.WordTrace tailWord_3025071 prefixEnd_3025071 1035543624651492753000305 := by
  unfold tailWord_3025071
  simp only [CollatzResearch.WordTrace]
  refine ⟨110333403623691882840019067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73555602415794588560012711 110333403623691882840019067)
  ·
    refine ⟨165500105435537824260028601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110333403623691882840019067 165500105435537824260028601)
    ·
      refine ⟨124125079076653368195021451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165500105435537824260028601 124125079076653368195021451)
      ·
        refine ⟨186187618614980052292532177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124125079076653368195021451 186187618614980052292532177)
        ·
          refine ⟨139640713961235039219399133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186187618614980052292532177 139640713961235039219399133)
          ·
            refine ⟨52365267735463139707274675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139640713961235039219399133 52365267735463139707274675)
            ·
              refine ⟨78547901603194709560912013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52365267735463139707274675 78547901603194709560912013)
              ·
                refine ⟨29455463101198016085342005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78547901603194709560912013 29455463101198016085342005)
                ·
                  refine ⟨2761449665737314008000813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29455463101198016085342005 2761449665737314008000813)
                  ·
                    refine ⟨1035543624651492753000305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761449665737314008000813 1035543624651492753000305)
                    ·
                      rfl

theorem cell22_3025071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_3025071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025071 prefixEnd_3025071 := by exact prefixLift 3025071
  have htrace : WordTrace (prefixWord ++ tailWord_3025071) baseStart_3025071 baseEnd_3025071 := by
    simpa [prefixWord, tailWord_3025071, baseEnd_3025071] using wordTrace_append hprefix tailTrace_3025071
  have hstable : (prefixWord ++ tailWord_3025071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025071).length < 2 ^ (prefixWord ++ tailWord_3025071).sum := by decide
  have hdescent : baseEnd_3025071 < baseStart_3025071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025131 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_3025131 : Nat := 118140960795 + 3025131 * 2 ^ 59
def prefixEnd_3025131 : Nat := 4983230072969 + 3 ^ 40 * 3025131 * 2
def baseEnd_3025131 : Nat := 1035564163877672596500121

theorem tailTrace_3025131 : CollatzResearch.WordTrace tailWord_3025131 prefixEnd_3025131 1035564163877672596500121 := by
  unfold tailWord_3025131
  simp only [CollatzResearch.WordTrace]
  refine ⟨110335592003474513087203247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73557061335649675391468831 110335592003474513087203247)
  ·
    refine ⟨165503388005211769630804871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110335592003474513087203247 165503388005211769630804871)
    ·
      refine ⟨248255082007817654446207307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165503388005211769630804871 248255082007817654446207307)
      ·
        refine ⟨372382623011726481669310961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248255082007817654446207307 372382623011726481669310961)
        ·
          refine ⟨279286967258794861251983221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372382623011726481669310961 279286967258794861251983221)
          ·
            refine ⟨26183153180512018242373427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279286967258794861251983221 26183153180512018242373427)
            ·
              refine ⟨39274729770768027363560141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26183153180512018242373427 39274729770768027363560141)
              ·
                refine ⟨14728023664038010261335053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39274729770768027363560141 14728023664038010261335053)
                ·
                  refine ⟨5523008874014253848000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14728023664038010261335053 5523008874014253848000645)
                  ·
                    refine ⟨1035564163877672596500121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5523008874014253848000645 1035564163877672596500121)
                    ·
                      rfl

theorem cell22_3025131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_3025131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025131 prefixEnd_3025131 := by exact prefixLift 3025131
  have htrace : WordTrace (prefixWord ++ tailWord_3025131) baseStart_3025131 baseEnd_3025131 := by
    simpa [prefixWord, tailWord_3025131, baseEnd_3025131] using wordTrace_append hprefix tailTrace_3025131
  have hstable : (prefixWord ++ tailWord_3025131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025131).length < 2 ^ (prefixWord ++ tailWord_3025131).sum := by decide
  have hdescent : baseEnd_3025131 < baseStart_3025131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025163 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 4]
def baseStart_3025163 : Nat := 118140960795 + 3025163 * 2 ^ 59
def prefixEnd_3025163 : Nat := 4983230072969 + 3 ^ 40 * 3025163 * 2
def baseEnd_3025163 : Nat := 345191706043878393233341

theorem tailTrace_3025163 : CollatzResearch.WordTrace tailWord_3025163 prefixEnd_3025163 345191706043878393233341 := by
  unfold tailWord_3025163
  simp only [CollatzResearch.WordTrace]
  refine ⟨110336759139358582552368143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73557839426239055034912095 110336759139358582552368143)
  ·
    refine ⟨165505138709037873828552215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110336759139358582552368143 165505138709037873828552215)
    ·
      refine ⟨248257708063556810742828323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165505138709037873828552215 248257708063556810742828323)
      ·
        refine ⟨372386562095335216114242485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248257708063556810742828323 372386562095335216114242485)
        ·
          refine ⟨34911240196437676510710233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372386562095335216114242485 34911240196437676510710233)
          ·
            refine ⟨26183430147328257383032675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34911240196437676510710233 26183430147328257383032675)
            ·
              refine ⟨39275145220992386074549013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26183430147328257383032675 39275145220992386074549013)
              ·
                refine ⟨1841022432234018097244485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39275145220992386074549013 1841022432234018097244485)
                ·
                  refine ⟨345191706043878393233341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841022432234018097244485 345191706043878393233341)
                  ·
                    rfl

theorem cell22_3025163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 4].length) (baseStart_3025163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025163 prefixEnd_3025163 := by exact prefixLift 3025163
  have htrace : WordTrace (prefixWord ++ tailWord_3025163) baseStart_3025163 baseEnd_3025163 := by
    simpa [prefixWord, tailWord_3025163, baseEnd_3025163] using wordTrace_append hprefix tailTrace_3025163
  have hstable : (prefixWord ++ tailWord_3025163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025163).length < 2 ^ (prefixWord ++ tailWord_3025163).sum := by decide
  have hdescent : baseEnd_3025163 < baseStart_3025163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025176 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3025176 : Nat := 118140960795 + 3025176 * 2 ^ 59
def prefixEnd_3025176 : Nat := 4983230072969 + 3 ^ 40 * 3025176 * 2
def baseEnd_3025176 : Nat := 1035579568297307479124983

theorem tailTrace_3025176 : CollatzResearch.WordTrace tailWord_3025176 prefixEnd_3025176 1035579568297307479124983 := by
  unfold tailWord_3025176
  simp only [CollatzResearch.WordTrace]
  refine ⟨55168616644155742886295691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73558155525540990515060921 55168616644155742886295691)
  ·
    refine ⟨82752924966233614329443537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55168616644155742886295691 82752924966233614329443537)
    ·
      refine ⟨62064693724675210747082653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82752924966233614329443537 62064693724675210747082653)
      ·
        refine ⟨23274260146753204030155995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62064693724675210747082653 23274260146753204030155995)
        ·
          refine ⟨34911390220129806045233993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23274260146753204030155995 34911390220129806045233993)
          ·
            refine ⟨26183542665097354533925495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34911390220129806045233993 26183542665097354533925495)
            ·
              refine ⟨39275313997646031800888243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26183542665097354533925495 39275313997646031800888243)
              ·
                refine ⟨58912970996469047701332365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39275313997646031800888243 58912970996469047701332365)
                ·
                  refine ⟨22092364123675892887999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58912970996469047701332365 22092364123675892887999637)
                  ·
                    refine ⟨1035579568297307479124983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22092364123675892887999637 1035579568297307479124983)
                    ·
                      rfl

theorem cell22_3025176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3025176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025176 prefixEnd_3025176 := by exact prefixLift 3025176
  have htrace : WordTrace (prefixWord ++ tailWord_3025176) baseStart_3025176 baseEnd_3025176 := by
    simpa [prefixWord, tailWord_3025176, baseEnd_3025176] using wordTrace_append hprefix tailTrace_3025176
  have hstable : (prefixWord ++ tailWord_3025176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025176).length < 2 ^ (prefixWord ++ tailWord_3025176).sum := by decide
  have hdescent : baseEnd_3025176 < baseStart_3025176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025182 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3025182 : Nat := 118140960795 + 3025182 * 2 ^ 59
def prefixEnd_3025182 : Nat := 4983230072969 + 3 ^ 40 * 3025182 * 2
def baseEnd_3025182 : Nat := 1035581622219925463474965

theorem tailTrace_3025182 : CollatzResearch.WordTrace tailWord_3025182 prefixEnd_3025182 1035581622219925463474965 := by
  unfold tailWord_3025182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792181515786218599663725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73558301417526499198206533 13792181515786218599663725)
  ·
    refine ⟨5172068068419831974873897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13792181515786218599663725 5172068068419831974873897)
    ·
      refine ⟨3879051051314873981155423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5172068068419831974873897 3879051051314873981155423)
      ·
        refine ⟨5818576576972310971733135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3879051051314873981155423 5818576576972310971733135)
        ·
          refine ⟨8727864865458466457599703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818576576972310971733135 8727864865458466457599703)
          ·
            refine ⟨13091797298187699686399555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8727864865458466457599703 13091797298187699686399555)
            ·
              refine ⟨19637695947281549529599333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13091797298187699686399555 19637695947281549529599333)
              ·
                refine ⟨3682067990115290536799875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19637695947281549529599333 3682067990115290536799875)
                ·
                  refine ⟨5523101985172935805199813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682067990115290536799875 5523101985172935805199813)
                  ·
                    refine ⟨1035581622219925463474965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5523101985172935805199813 1035581622219925463474965)
                    ·
                      rfl

theorem cell22_3025182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3025182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025182 prefixEnd_3025182 := by exact prefixLift 3025182
  have htrace : WordTrace (prefixWord ++ tailWord_3025182) baseStart_3025182 baseEnd_3025182 := by
    simpa [prefixWord, tailWord_3025182, baseEnd_3025182] using wordTrace_append hprefix tailTrace_3025182
  have hstable : (prefixWord ++ tailWord_3025182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025182).length < 2 ^ (prefixWord ++ tailWord_3025182).sum := by decide
  have hdescent : baseEnd_3025182 < baseStart_3025182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025246 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3025246 : Nat := 118140960795 + 3025246 * 2 ^ 59
def prefixEnd_3025246 : Nat := 4983230072969 + 3 ^ 40 * 3025246 * 2
def baseEnd_3025246 : Nat := 1035603530727850629874769

theorem tailTrace_3025246 : CollatzResearch.WordTrace tailWord_3025246 prefixEnd_3025246 1035603530727850629874769 := by
  unfold tailWord_3025246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792473299757235965954949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73559857598705258485093061 13792473299757235965954949)
  ·
    refine ⟨2586088743704481743616553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13792473299757235965954949 2586088743704481743616553)
    ·
      refine ⟨1939566557778361307712415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2586088743704481743616553 1939566557778361307712415)
      ·
        refine ⟨2909349836667541961568623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939566557778361307712415 2909349836667541961568623)
        ·
          refine ⟨4364024755001312942352935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909349836667541961568623 4364024755001312942352935)
          ·
            refine ⟨6546037132501969413529403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364024755001312942352935 6546037132501969413529403)
            ·
              refine ⟨9819055698752954120294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546037132501969413529403 9819055698752954120294105)
              ·
                refine ⟨7364291774064715590220579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819055698752954120294105 7364291774064715590220579)
                ·
                  refine ⟨11046437661097073385330869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364291774064715590220579 11046437661097073385330869)
                  ·
                    refine ⟨1035603530727850629874769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11046437661097073385330869 1035603530727850629874769)
                    ·
                      rfl

theorem cell22_3025246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3025246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025246 prefixEnd_3025246 := by exact prefixLift 3025246
  have htrace : WordTrace (prefixWord ++ tailWord_3025246) baseStart_3025246 baseEnd_3025246 := by
    simpa [prefixWord, tailWord_3025246, baseEnd_3025246] using wordTrace_append hprefix tailTrace_3025246
  have hstable : (prefixWord ++ tailWord_3025246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025246).length < 2 ^ (prefixWord ++ tailWord_3025246).sum := by decide
  have hdescent : baseEnd_3025246 < baseStart_3025246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025315 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 4]
def baseStart_3025315 : Nat := 118140960795 + 3025315 * 2 ^ 59
def prefixEnd_3025315 : Nat := 4983230072969 + 3 ^ 40 * 3025315 * 2
def baseEnd_3025315 : Nat := 345209050279319149966519

theorem tailTrace_3025315 : CollatzResearch.WordTrace tailWord_3025315 prefixEnd_3025315 345209050279319149966519 := by
  unfold tailWord_3025315
  simp only [CollatzResearch.WordTrace]
  refine ⟨110342303034807912511901399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73561535356538608341267599 110342303034807912511901399)
  ·
    refine ⟨165513454552211868767852099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110342303034807912511901399 165513454552211868767852099)
    ·
      refine ⟨248270181828317803151778149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165513454552211868767852099 248270181828317803151778149)
      ·
        refine ⟨46550659092809588090958403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248270181828317803151778149 46550659092809588090958403)
        ·
          refine ⟨69825988639214382136437605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46550659092809588090958403 69825988639214382136437605)
          ·
            refine ⟨13092372869852696650582051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69825988639214382136437605 13092372869852696650582051)
            ·
              refine ⟨19638559304779044975873077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13092372869852696650582051 19638559304779044975873077)
              ·
                refine ⟨1841114934823035466488101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19638559304779044975873077 1841114934823035466488101)
                ·
                  refine ⟨345209050279319149966519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841114934823035466488101 345209050279319149966519)
                  ·
                    rfl

theorem cell22_3025315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 4].length) (baseStart_3025315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025315 prefixEnd_3025315 := by exact prefixLift 3025315
  have htrace : WordTrace (prefixWord ++ tailWord_3025315) baseStart_3025315 baseEnd_3025315 := by
    simpa [prefixWord, tailWord_3025315, baseEnd_3025315] using wordTrace_append hprefix tailTrace_3025315
  have hstable : (prefixWord ++ tailWord_3025315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025315).length < 2 ^ (prefixWord ++ tailWord_3025315).sum := by decide
  have hdescent : baseEnd_3025315 < baseStart_3025315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025330 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3025330 : Nat := 118140960795 + 3025330 * 2 ^ 59
def prefixEnd_3025330 : Nat := 4983230072969 + 3 ^ 40 * 3025330 * 2
def baseEnd_3025330 : Nat := 1035632285644502410774511

theorem tailTrace_3025330 : CollatzResearch.WordTrace tailWord_3025330 prefixEnd_3025330 1035632285644502410774511 := by
  unfold tailWord_3025330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27585712532438392518424361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73561900086502380049131629 27585712532438392518424361)
  ·
    refine ⟨20689284399328794388818271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27585712532438392518424361 20689284399328794388818271)
    ·
      refine ⟨31033926598993191583227407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20689284399328794388818271 31033926598993191583227407)
      ·
        refine ⟨46550889898489787374841111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31033926598993191583227407 46550889898489787374841111)
        ·
          refine ⟨69826334847734681062261667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46550889898489787374841111 69826334847734681062261667)
          ·
            refine ⟨104739502271602021593392501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69826334847734681062261667 104739502271602021593392501)
            ·
              refine ⟨9819328337962689524380547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104739502271602021593392501 9819328337962689524380547)
              ·
                refine ⟨14728992506944034286570821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9819328337962689524380547 14728992506944034286570821)
                ·
                  refine ⟨2761686095052006428732029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14728992506944034286570821 2761686095052006428732029)
                  ·
                    refine ⟨1035632285644502410774511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761686095052006428732029 1035632285644502410774511)
                    ·
                      rfl

theorem cell22_3025330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3025330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025330 prefixEnd_3025330 := by exact prefixLift 3025330
  have htrace : WordTrace (prefixWord ++ tailWord_3025330) baseStart_3025330 baseEnd_3025330 := by
    simpa [prefixWord, tailWord_3025330, baseEnd_3025330] using wordTrace_append hprefix tailTrace_3025330
  have hstable : (prefixWord ++ tailWord_3025330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025330).length < 2 ^ (prefixWord ++ tailWord_3025330).sum := by decide
  have hdescent : baseEnd_3025330 < baseStart_3025330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025358 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3025358 : Nat := 118140960795 + 3025358 * 2 ^ 59
def prefixEnd_3025358 : Nat := 4983230072969 + 3 ^ 40 * 3025358 * 2
def baseEnd_3025358 : Nat := 1035641870616719671074425

theorem tailTrace_3025358 : CollatzResearch.WordTrace tailWord_3025358 prefixEnd_3025358 1035641870616719671074425 := by
  unfold tailWord_3025358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792983921706516356964591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73562580915768087237144485 13792983921706516356964591)
  ·
    refine ⟨20689475882559774535446887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13792983921706516356964591 20689475882559774535446887)
    ·
      refine ⟨31034213823839661803170331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20689475882559774535446887 31034213823839661803170331)
      ·
        refine ⟨46551320735759492704755497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31034213823839661803170331 46551320735759492704755497)
        ·
          refine ⟨34913490551819619528566623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46551320735759492704755497 34913490551819619528566623)
          ·
            refine ⟨52370235827729429292849935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34913490551819619528566623 52370235827729429292849935)
            ·
              refine ⟨78555353741594143939274903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52370235827729429292849935 78555353741594143939274903)
              ·
                refine ⟨117833030612391215908912355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78555353741594143939274903 117833030612391215908912355)
                ·
                  refine ⟨176749545918586823863368533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117833030612391215908912355 176749545918586823863368533)
                  ·
                    refine ⟨1035641870616719671074425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176749545918586823863368533 1035641870616719671074425)
                    ·
                      rfl

theorem cell22_3025358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3025358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025358 prefixEnd_3025358 := by exact prefixLift 3025358
  have htrace : WordTrace (prefixWord ++ tailWord_3025358) baseStart_3025358 baseEnd_3025358 := by
    simpa [prefixWord, tailWord_3025358, baseEnd_3025358] using wordTrace_append hprefix tailTrace_3025358
  have hstable : (prefixWord ++ tailWord_3025358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025358).length < 2 ^ (prefixWord ++ tailWord_3025358).sum := by decide
  have hdescent : baseEnd_3025358 < baseStart_3025358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025388 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_3025388 : Nat := 118140960795 + 3025388 * 2 ^ 59
def prefixEnd_3025388 : Nat := 4983230072969 + 3 ^ 40 * 3025388 * 2
def baseEnd_3025388 : Nat := 345217380076603197608111

theorem tailTrace_3025388 : CollatzResearch.WordTrace tailWord_3025388 prefixEnd_3025388 345217380076603197608111 := by
  unfold tailWord_3025388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55172482781771722989654409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73563310375695630652872545 55172482781771722989654409)
  ·
    refine ⟨41379362086328792242240807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55172482781771722989654409 41379362086328792242240807)
    ·
      refine ⟨62069043129493188363361211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41379362086328792242240807 62069043129493188363361211)
      ·
        refine ⟨93103564694239782545041817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62069043129493188363361211 93103564694239782545041817)
        ·
          refine ⟨69827673520679836908781363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93103564694239782545041817 69827673520679836908781363)
          ·
            refine ⟨104741510281019755363172045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69827673520679836908781363 104741510281019755363172045)
            ·
              refine ⟨39278066355382408261189517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104741510281019755363172045 39278066355382408261189517)
              ·
                refine ⟨14729274883268403097946069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39278066355382408261189517 14729274883268403097946069)
                ·
                  refine ⟨345217380076603197608111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14729274883268403097946069 345217380076603197608111)
                  ·
                    rfl

theorem cell22_3025388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_3025388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025388 prefixEnd_3025388 := by exact prefixLift 3025388
  have htrace : WordTrace (prefixWord ++ tailWord_3025388) baseStart_3025388 baseEnd_3025388 := by
    simpa [prefixWord, tailWord_3025388, baseEnd_3025388] using wordTrace_append hprefix tailTrace_3025388
  have hstable : (prefixWord ++ tailWord_3025388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025388).length < 2 ^ (prefixWord ++ tailWord_3025388).sum := by decide
  have hdescent : baseEnd_3025388 < baseStart_3025388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025405 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3025405 : Nat := 118140960795 + 3025405 * 2 ^ 59
def prefixEnd_3025405 : Nat := 4983230072969 + 3 ^ 40 * 3025405 * 2
def baseEnd_3025405 : Nat := 345219319892409071716427

theorem tailTrace_3025405 : CollatzResearch.WordTrace tailWord_3025405 prefixEnd_3025405 345219319892409071716427 := by
  unfold tailWord_3025405
  simp only [CollatzResearch.WordTrace]
  refine ⟨110345585604481857882677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73563723736321238588451779 110345585604481857882677669)
  ·
    refine ⟨20689797300840348353002063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110345585604481857882677669 20689797300840348353002063)
    ·
      refine ⟨31034695951260522529503095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20689797300840348353002063 31034695951260522529503095)
      ·
        refine ⟨46552043926890783794254643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31034695951260522529503095 46552043926890783794254643)
        ·
          refine ⟨69828065890336175691381965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46552043926890783794254643 69828065890336175691381965)
          ·
            refine ⟨26185524708876065884268237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69828065890336175691381965 26185524708876065884268237)
            ·
              refine ⟨9819571765828524706600589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26185524708876065884268237 9819571765828524706600589)
              ·
                refine ⟨3682339412185696764975221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9819571765828524706600589 3682339412185696764975221)
                ·
                  refine ⟨345219319892409071716427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3682339412185696764975221 345219319892409071716427)
                  ·
                    rfl

theorem cell22_3025405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3025405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025405 prefixEnd_3025405 := by exact prefixLift 3025405
  have htrace : WordTrace (prefixWord ++ tailWord_3025405) baseStart_3025405 baseEnd_3025405 := by
    simpa [prefixWord, tailWord_3025405, baseEnd_3025405] using wordTrace_append hprefix tailTrace_3025405
  have hstable : (prefixWord ++ tailWord_3025405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025405).length < 2 ^ (prefixWord ++ tailWord_3025405).sum := by decide
  have hdescent : baseEnd_3025405 < baseStart_3025405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025433 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 8]
def baseStart_3025433 : Nat := 118140960795 + 3025433 * 2 ^ 59
def prefixEnd_3025433 : Nat := 4983230072969 + 3 ^ 40 * 3025433 * 2
def baseEnd_3025433 : Nat := 345222514883148158483065

theorem tailTrace_3025433 : CollatzResearch.WordTrace tailWord_3025433 prefixEnd_3025433 345222514883148158483065 := by
  unfold tailWord_3025433
  simp only [CollatzResearch.WordTrace]
  refine ⟨110346606848380418664696953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73564404565586945776464635 110346606848380418664696953)
  ·
    refine ⟨82759955136285313998522715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110346606848380418664696953 82759955136285313998522715)
    ·
      refine ⟨124139932704427970997784073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82759955136285313998522715 124139932704427970997784073)
      ·
        refine ⟨93104949528320978248338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124139932704427970997784073 93104949528320978248338055)
        ·
          refine ⟨139657424292481467372507083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93104949528320978248338055 139657424292481467372507083)
          ·
            refine ⟨209486136438722201058760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139657424292481467372507083 209486136438722201058760625)
            ·
              refine ⟨157114602329041650794070469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209486136438722201058760625 157114602329041650794070469)
              ·
                refine ⟨29458987936695309523888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157114602329041650794070469 29458987936695309523888213)
                ·
                  refine ⟨345222514883148158483065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29458987936695309523888213 345222514883148158483065)
                  ·
                    rfl

theorem cell22_3025433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_3025433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025433 prefixEnd_3025433 := by exact prefixLift 3025433
  have htrace : WordTrace (prefixWord ++ tailWord_3025433) baseStart_3025433 baseEnd_3025433 := by
    simpa [prefixWord, tailWord_3025433, baseEnd_3025433] using wordTrace_append hprefix tailTrace_3025433
  have hstable : (prefixWord ++ tailWord_3025433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025433).length < 2 ^ (prefixWord ++ tailWord_3025433).sum := by decide
  have hdescent : baseEnd_3025433 < baseStart_3025433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025527 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 3, 3]
def baseStart_3025527 : Nat := 118140960795 + 3025527 * 2 ^ 59
def prefixEnd_3025527 : Nat := 4983230072969 + 3 ^ 40 * 3025527 * 2
def baseEnd_3025527 : Nat := 1035699722770459563598907

theorem tailTrace_3025527 : CollatzResearch.WordTrace tailWord_3025527 prefixEnd_3025527 1035699722770459563598907 := by
  unfold tailWord_3025527
  simp only [CollatzResearch.WordTrace]
  refine ⟨110350035310039872718618835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73566690206693248479079223 110350035310039872718618835)
  ·
    refine ⟨165525052965059809077928253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110350035310039872718618835 165525052965059809077928253)
    ·
      refine ⟨62071894861897428404223095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165525052965059809077928253 62071894861897428404223095)
      ·
        refine ⟨93107842292846142606334643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62071894861897428404223095 93107842292846142606334643)
        ·
          refine ⟨139661763439269213909501965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93107842292846142606334643 139661763439269213909501965)
          ·
            refine ⟨52373161289725955216063237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139661763439269213909501965 52373161289725955216063237)
            ·
              refine ⟨9819967741823616603011857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52373161289725955216063237 9819967741823616603011857)
              ·
                refine ⟨7364975806367712452258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819967741823616603011857 7364975806367712452258893)
                ·
                  refine ⟨2761865927387892169597085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7364975806367712452258893 2761865927387892169597085)
                  ·
                    refine ⟨1035699722770459563598907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761865927387892169597085 1035699722770459563598907)
                    ·
                      rfl

theorem cell22_3025527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_3025527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025527 prefixEnd_3025527 := by exact prefixLift 3025527
  have htrace : WordTrace (prefixWord ++ tailWord_3025527) baseStart_3025527 baseEnd_3025527 := by
    simpa [prefixWord, tailWord_3025527, baseEnd_3025527] using wordTrace_append hprefix tailTrace_3025527
  have hstable : (prefixWord ++ tailWord_3025527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025527).length < 2 ^ (prefixWord ++ tailWord_3025527).sum := by decide
  have hdescent : baseEnd_3025527 < baseStart_3025527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025561 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_3025561 : Nat := 118140960795 + 3025561 * 2 ^ 59
def prefixEnd_3025561 : Nat := 4983230072969 + 3 ^ 40 * 3025561 * 2
def baseEnd_3025561 : Nat := 1035711361665294808248803

theorem tailTrace_3025561 : CollatzResearch.WordTrace tailWord_3025561 prefixEnd_3025561 1035711361665294808248803 := by
  unfold tailWord_3025561
  simp only [CollatzResearch.WordTrace]
  refine ⟨110351275391916696525356537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73567516927944464350237691 110351275391916696525356537)
  ·
    refine ⟨82763456543937522394017403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110351275391916696525356537 82763456543937522394017403)
    ·
      refine ⟨124145184815906283591026105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82763456543937522394017403 124145184815906283591026105)
      ·
        refine ⟨93108888611929712693269579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124145184815906283591026105 93108888611929712693269579)
        ·
          refine ⟨139663332917894569039904369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93108888611929712693269579 139663332917894569039904369)
          ·
            refine ⟨104747499688420926779928277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139663332917894569039904369 104747499688420926779928277)
            ·
              refine ⟨2455019523947365471404569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104747499688420926779928277 2455019523947365471404569)
              ·
                refine ⟨1841264642960524103553427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455019523947365471404569 1841264642960524103553427)
                ·
                  refine ⟨2761896964440786155330141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841264642960524103553427 2761896964440786155330141)
                  ·
                    refine ⟨1035711361665294808248803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761896964440786155330141 1035711361665294808248803)
                    ·
                      rfl

theorem cell22_3025561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_3025561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025561 prefixEnd_3025561 := by exact prefixLift 3025561
  have htrace : WordTrace (prefixWord ++ tailWord_3025561) baseStart_3025561 baseEnd_3025561 := by
    simpa [prefixWord, tailWord_3025561, baseEnd_3025561] using wordTrace_append hprefix tailTrace_3025561
  have hstable : (prefixWord ++ tailWord_3025561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025561).length < 2 ^ (prefixWord ++ tailWord_3025561).sum := by decide
  have hdescent : baseEnd_3025561 < baseStart_3025561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025587 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_3025587 : Nat := 118140960795 + 3025587 * 2 ^ 59
def prefixEnd_3025587 : Nat := 4983230072969 + 3 ^ 40 * 3025587 * 2
def baseEnd_3025587 : Nat := 1035720261996639407098723

theorem tailTrace_3025587 : CollatzResearch.WordTrace tailWord_3025587 prefixEnd_3025587 1035720261996639407098723 := by
  unfold tailWord_3025587
  simp only [CollatzResearch.WordTrace]
  refine ⟨110352223689822502965803015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73568149126548335310535343 110352223689822502965803015)
  ·
    refine ⟨165528335534733754448704523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110352223689822502965803015 165528335534733754448704523)
    ·
      refine ⟨248292503302100631673056785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165528335534733754448704523 248292503302100631673056785)
      ·
        refine ⟨186219377476575473754792589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248292503302100631673056785 186219377476575473754792589)
        ·
          refine ⟨69832266553715802658047221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186219377476575473754792589 69832266553715802658047221)
          ·
            refine ⟨6546774989410856499191927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69832266553715802658047221 6546774989410856499191927)
            ·
              refine ⟨9820162484116284748787891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546774989410856499191927 9820162484116284748787891)
              ·
                refine ⟨14730243726174427123181837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9820162484116284748787891 14730243726174427123181837)
                ·
                  refine ⟨5523841397315410171193189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14730243726174427123181837 5523841397315410171193189)
                  ·
                    refine ⟨1035720261996639407098723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5523841397315410171193189 1035720261996639407098723)
                    ·
                      rfl

theorem cell22_3025587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_3025587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025587 prefixEnd_3025587 := by exact prefixLift 3025587
  have htrace : WordTrace (prefixWord ++ tailWord_3025587) baseStart_3025587 baseEnd_3025587 := by
    simpa [prefixWord, tailWord_3025587, baseEnd_3025587] using wordTrace_append hprefix tailTrace_3025587
  have hstable : (prefixWord ++ tailWord_3025587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025587).length < 2 ^ (prefixWord ++ tailWord_3025587).sum := by decide
  have hdescent : baseEnd_3025587 < baseStart_3025587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025615 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3025615 : Nat := 118140960795 + 3025615 * 2 ^ 59
def prefixEnd_3025615 : Nat := 4983230072969 + 3 ^ 40 * 3025615 * 2
def baseEnd_3025615 : Nat := 1035729846968856667398637

theorem tailTrace_3025615 : CollatzResearch.WordTrace tailWord_3025615 prefixEnd_3025615 1035729846968856667398637 := by
  unfold tailWord_3025615
  simp only [CollatzResearch.WordTrace]
  refine ⟨110353244933721063747822299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73568829955814042498548199 110353244933721063747822299)
  ·
    refine ⟨165529867400581595621733449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110353244933721063747822299 165529867400581595621733449)
    ·
      refine ⟨124147400550436196716300087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165529867400581595621733449 124147400550436196716300087)
      ·
        refine ⟨186221100825654295074450131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124147400550436196716300087 186221100825654295074450131)
        ·
          refine ⟨279331651238481442611675197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186221100825654295074450131 279331651238481442611675197)
          ·
            refine ⟨104749369214430540979378199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279331651238481442611675197 104749369214430540979378199)
            ·
              refine ⟨157124053821645811469067299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104749369214430540979378199 157124053821645811469067299)
              ·
                refine ⟨235686080732468717203600949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157124053821645811469067299 235686080732468717203600949)
                ·
                  refine ⟨22095570068668942237837589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235686080732468717203600949 22095570068668942237837589)
                  ·
                    refine ⟨1035729846968856667398637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22095570068668942237837589 1035729846968856667398637)
                    ·
                      rfl

theorem cell22_3025615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3025615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025615 prefixEnd_3025615 := by exact prefixLift 3025615
  have htrace : WordTrace (prefixWord ++ tailWord_3025615) baseStart_3025615 baseEnd_3025615 := by
    simpa [prefixWord, tailWord_3025615, baseEnd_3025615] using wordTrace_append hprefix tailTrace_3025615
  have hstable : (prefixWord ++ tailWord_3025615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025615).length < 2 ^ (prefixWord ++ tailWord_3025615).sum := by decide
  have hdescent : baseEnd_3025615 < baseStart_3025615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025679 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 3, 3]
def baseStart_3025679 : Nat := 118140960795 + 3025679 * 2 ^ 59
def prefixEnd_3025679 : Nat := 4983230072969 + 3 ^ 40 * 3025679 * 2
def baseEnd_3025679 : Nat := 1035751755476781833798441

theorem tailTrace_3025679 : CollatzResearch.WordTrace tailWord_3025679 prefixEnd_3025679 1035751755476781833798441 := by
  unfold tailWord_3025679
  simp only [CollatzResearch.WordTrace]
  refine ⟨110355579205489202678152091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73570386136992801785434727 110355579205489202678152091)
  ·
    refine ⟨165533368808233804017228137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110355579205489202678152091 165533368808233804017228137)
    ·
      refine ⟨124150026606175353012921103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165533368808233804017228137 124150026606175353012921103)
      ·
        refine ⟨186225039909263029519381655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124150026606175353012921103 186225039909263029519381655)
        ·
          refine ⟨279337559863894544279072483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186225039909263029519381655 279337559863894544279072483)
          ·
            refine ⟨419006339795841816418608725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279337559863894544279072483 419006339795841816418608725)
            ·
              refine ⟨4910230544482521286155571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 419006339795841816418608725 4910230544482521286155571)
              ·
                refine ⟨7365345816723781929233357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910230544482521286155571 7365345816723781929233357)
                ·
                  refine ⟨2762004681271418223462509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7365345816723781929233357 2762004681271418223462509)
                  ·
                    refine ⟨1035751755476781833798441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762004681271418223462509 1035751755476781833798441)
                    ·
                      rfl

theorem cell22_3025679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_3025679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025679 prefixEnd_3025679 := by exact prefixLift 3025679
  have htrace : WordTrace (prefixWord ++ tailWord_3025679) baseStart_3025679 baseEnd_3025679 := by
    simpa [prefixWord, tailWord_3025679, baseEnd_3025679] using wordTrace_append hprefix tailTrace_3025679
  have hstable : (prefixWord ++ tailWord_3025679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025679).length < 2 ^ (prefixWord ++ tailWord_3025679).sum := by decide
  have hdescent : baseEnd_3025679 < baseStart_3025679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025752 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3025752 : Nat := 118140960795 + 3025752 * 2 ^ 59
def prefixEnd_3025752 : Nat := 4983230072969 + 3 ^ 40 * 3025752 * 2
def baseEnd_3025752 : Nat := 1035776744868633976723217

theorem tailTrace_3025752 : CollatzResearch.WordTrace tailWord_3025752 prefixEnd_3025752 1035776744868633976723217 := by
  unfold tailWord_3025752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55179120867112368072779755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73572161156149824097039673 55179120867112368072779755)
  ·
    refine ⟨82768681300668552109169633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55179120867112368072779755 82768681300668552109169633)
    ·
      refine ⟨62076510975501414081877225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82768681300668552109169633 62076510975501414081877225)
      ·
        refine ⟨46557383231626060561407919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62076510975501414081877225 46557383231626060561407919)
        ·
          refine ⟨69836074847439090842111879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46557383231626060561407919 69836074847439090842111879)
          ·
            refine ⟨104754112271158636263167819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69836074847439090842111879 104754112271158636263167819)
            ·
              refine ⟨157131168406737954394751729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104754112271158636263167819 157131168406737954394751729)
              ·
                refine ⟨117848376305053465796063797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157131168406737954394751729 117848376305053465796063797)
                ·
                  refine ⟨11048285278598762418380981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117848376305053465796063797 11048285278598762418380981)
                  ·
                    refine ⟨1035776744868633976723217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11048285278598762418380981 1035776744868633976723217)
                    ·
                      rfl

theorem cell22_3025752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3025752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025752 prefixEnd_3025752 := by exact prefixLift 3025752
  have htrace : WordTrace (prefixWord ++ tailWord_3025752) baseStart_3025752 baseEnd_3025752 := by
    simpa [prefixWord, tailWord_3025752, baseEnd_3025752] using wordTrace_append hprefix tailTrace_3025752
  have hstable : (prefixWord ++ tailWord_3025752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025752).length < 2 ^ (prefixWord ++ tailWord_3025752).sum := by decide
  have hdescent : baseEnd_3025752 < baseStart_3025752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025756 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3025756 : Nat := 118140960795 + 3025756 * 2 ^ 59
def prefixEnd_3025756 : Nat := 4983230072969 + 3 ^ 40 * 3025756 * 2
def baseEnd_3025756 : Nat := 1035778114150379299623205

theorem tailTrace_3025756 : CollatzResearch.WordTrace tailWord_3025756 prefixEnd_3025756 1035778114150379299623205 := by
  unfold tailWord_3025756
  simp only [CollatzResearch.WordTrace]
  refine ⟨55179193813105122414352561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73572258417473496552470081 55179193813105122414352561)
  ·
    refine ⟨41384395359828841810764421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55179193813105122414352561 41384395359828841810764421)
    ·
      refine ⟨7759574129967907839518329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41384395359828841810764421 7759574129967907839518329)
      ·
        refine ⟨5819680597475930879638747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7759574129967907839518329 5819680597475930879638747)
        ·
          refine ⟨8729520896213896319458121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819680597475930879638747 8729520896213896319458121)
          ·
            refine ⟨6547140672160422239593591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729520896213896319458121 6547140672160422239593591)
            ·
              refine ⟨9820711008240633359390387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547140672160422239593591 9820711008240633359390387)
              ·
                refine ⟨14731066512360950039085581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9820711008240633359390387 14731066512360950039085581)
                ·
                  refine ⟨5524149942135356264657093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14731066512360950039085581 5524149942135356264657093)
                  ·
                    refine ⟨1035778114150379299623205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524149942135356264657093 1035778114150379299623205)
                    ·
                      rfl

theorem cell22_3025756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3025756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025756 prefixEnd_3025756 := by exact prefixLift 3025756
  have htrace : WordTrace (prefixWord ++ tailWord_3025756) baseStart_3025756 baseEnd_3025756 := by
    simpa [prefixWord, tailWord_3025756, baseEnd_3025756] using wordTrace_append hprefix tailTrace_3025756
  have hstable : (prefixWord ++ tailWord_3025756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025756).length < 2 ^ (prefixWord ++ tailWord_3025756).sum := by decide
  have hdescent : baseEnd_3025756 < baseStart_3025756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025799 : List Nat := [1, 1, 4, 2, 3, 1, 3, 7]
def baseStart_3025799 : Nat := 118140960795 + 3025799 * 2 ^ 59
def prefixEnd_3025799 : Nat := 4983230072969 + 3 ^ 40 * 3025799 * 2
def baseEnd_3025799 : Nat := 115088092658793502310897

theorem tailTrace_3025799 : CollatzResearch.WordTrace tailWord_3025799 prefixEnd_3025799 115088092658793502310897 := by
  unfold tailWord_3025799
  simp only [CollatzResearch.WordTrace]
  refine ⟨110359955965054463172520451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73573303976702975448346967 110359955965054463172520451)
  ·
    refine ⟨165539933947581694758780677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110359955965054463172520451 165539933947581694758780677)
    ·
      refine ⟨31038737615171567767271377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165539933947581694758780677 31038737615171567767271377)
      ·
        refine ⟨23279053211378675825453533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31038737615171567767271377 23279053211378675825453533)
        ·
          refine ⟨8729644954267003434545075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23279053211378675825453533 8729644954267003434545075)
          ·
            refine ⟨13094467431400505151817613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729644954267003434545075 13094467431400505151817613)
            ·
              refine ⟨4910425286775189431931605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13094467431400505151817613 4910425286775189431931605)
              ·
                refine ⟨115088092658793502310897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4910425286775189431931605 115088092658793502310897)
                ·
                  rfl

theorem cell22_3025799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 7].length) (baseStart_3025799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025799 prefixEnd_3025799 := by exact prefixLift 3025799
  have htrace : WordTrace (prefixWord ++ tailWord_3025799) baseStart_3025799 baseEnd_3025799 := by
    simpa [prefixWord, tailWord_3025799, baseEnd_3025799] using wordTrace_append hprefix tailTrace_3025799
  have hstable : (prefixWord ++ tailWord_3025799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025799).length < 2 ^ (prefixWord ++ tailWord_3025799).sum := by decide
  have hdescent : baseEnd_3025799 < baseStart_3025799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025818 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_3025818 : Nat := 118140960795 + 3025818 * 2 ^ 59
def prefixEnd_3025818 : Nat := 4983230072969 + 3 ^ 40 * 3025818 * 2
def baseEnd_3025818 : Nat := 1035799338017431804573015

theorem tailTrace_3025818 : CollatzResearch.WordTrace tailWord_3025818 prefixEnd_3025818 1035799338017431804573015 := by
  unfold tailWord_3025818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590162237996407354365527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73573765967990419611641405 27590162237996407354365527)
  ·
    refine ⟨41385243356994611031548291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590162237996407354365527 41385243356994611031548291)
    ·
      refine ⟨62077865035491916547322437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41385243356994611031548291 62077865035491916547322437)
      ·
        refine ⟨11639599694154734352622957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62077865035491916547322437 11639599694154734352622957)
        ·
          refine ⟨4364849885308025382233609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11639599694154734352622957 4364849885308025382233609)
          ·
            refine ⟨3273637413981019036675207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4364849885308025382233609 3273637413981019036675207)
            ·
              refine ⟨4910456120971528555012811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273637413981019036675207 4910456120971528555012811)
              ·
                refine ⟨7365684181457292832519217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910456120971528555012811 7365684181457292832519217)
                ·
                  refine ⟨5524263136092969624389413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365684181457292832519217 5524263136092969624389413)
                  ·
                    refine ⟨1035799338017431804573015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524263136092969624389413 1035799338017431804573015)
                    ·
                      rfl

theorem cell22_3025818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_3025818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025818 prefixEnd_3025818 := by exact prefixLift 3025818
  have htrace : WordTrace (prefixWord ++ tailWord_3025818) baseStart_3025818 baseEnd_3025818 := by
    simpa [prefixWord, tailWord_3025818, baseEnd_3025818] using wordTrace_append hprefix tailTrace_3025818
  have hstable : (prefixWord ++ tailWord_3025818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025818).length < 2 ^ (prefixWord ++ tailWord_3025818).sum := by decide
  have hdescent : baseEnd_3025818 < baseStart_3025818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025837 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3025837 : Nat := 118140960795 + 3025837 * 2 ^ 59
def prefixEnd_3025837 : Nat := 4983230072969 + 3 ^ 40 * 3025837 * 2
def baseEnd_3025837 : Nat := 1035805842105722088347957

theorem tailTrace_3025837 : CollatzResearch.WordTrace tailWord_3025837 prefixEnd_3025837 1035805842105722088347957 := by
  unfold tailWord_3025837
  simp only [CollatzResearch.WordTrace]
  refine ⟨110361341938916795662403765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73574227959277863774935843 110361341938916795662403765)
  ·
    refine ⟨10346375806773449593350353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110361341938916795662403765 10346375806773449593350353)
    ·
      refine ⟨7759781855080087195012765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10346375806773449593350353 7759781855080087195012765)
      ·
        refine ⟨2909918195655032698129787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7759781855080087195012765 2909918195655032698129787)
        ·
          refine ⟨4364877293482549047194681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909918195655032698129787 4364877293482549047194681)
          ·
            refine ⟨3273657970111911785396011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4364877293482549047194681 3273657970111911785396011)
            ·
              refine ⟨4910486955167867678094017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273657970111911785396011 4910486955167867678094017)
              ·
                refine ⟨3682865216375900758570513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910486955167867678094017 3682865216375900758570513)
                ·
                  refine ⟨2762148912281925568927885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682865216375900758570513 2762148912281925568927885)
                  ·
                    refine ⟨1035805842105722088347957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762148912281925568927885 1035805842105722088347957)
                    ·
                      rfl

theorem cell22_3025837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3025837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025837 prefixEnd_3025837 := by exact prefixLift 3025837
  have htrace : WordTrace (prefixWord ++ tailWord_3025837) baseStart_3025837 baseEnd_3025837 := by
    simpa [prefixWord, tailWord_3025837, baseEnd_3025837] using wordTrace_append hprefix tailTrace_3025837
  have hstable : (prefixWord ++ tailWord_3025837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025837).length < 2 ^ (prefixWord ++ tailWord_3025837).sum := by decide
  have hdescent : baseEnd_3025837 < baseStart_3025837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025848 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_3025848 : Nat := 118140960795 + 3025848 * 2 ^ 59
def prefixEnd_3025848 : Nat := 4983230072969 + 3 ^ 40 * 3025848 * 2
def baseEnd_3025848 : Nat := 1035809607630521726322923

theorem tailTrace_3025848 : CollatzResearch.WordTrace tailWord_3025848 prefixEnd_3025848 1035809607630521726322923 := by
  unfold tailWord_3025848
  simp only [CollatzResearch.WordTrace]
  refine ⟨55180871570938472270527099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73574495427917963027369465 55180871570938472270527099)
  ·
    refine ⟨82771307356407708405790649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55180871570938472270527099 82771307356407708405790649)
    ·
      refine ⟨62078480517305781304342987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82771307356407708405790649 62078480517305781304342987)
      ·
        refine ⟨93117720775958671956514481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62078480517305781304342987 93117720775958671956514481)
        ·
          refine ⟨69838290581969003967385861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93117720775958671956514481 69838290581969003967385861)
          ·
            refine ⟨13094679484119188243884849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69838290581969003967385861 13094679484119188243884849)
            ·
              refine ⟨9821009613089391182913637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094679484119188243884849 9821009613089391182913637)
              ·
                refine ⟨1841439302454260846796307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9821009613089391182913637 1841439302454260846796307)
                ·
                  refine ⟨2762158953681391270194461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841439302454260846796307 2762158953681391270194461)
                  ·
                    refine ⟨1035809607630521726322923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762158953681391270194461 1035809607630521726322923)
                    ·
                      rfl

theorem cell22_3025848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_3025848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025848 prefixEnd_3025848 := by exact prefixLift 3025848
  have htrace : WordTrace (prefixWord ++ tailWord_3025848) baseStart_3025848 baseEnd_3025848 := by
    simpa [prefixWord, tailWord_3025848, baseEnd_3025848] using wordTrace_append hprefix tailTrace_3025848
  have hstable : (prefixWord ++ tailWord_3025848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025848).length < 2 ^ (prefixWord ++ tailWord_3025848).sum := by decide
  have hdescent : baseEnd_3025848 < baseStart_3025848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025891 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 1, 4]
def baseStart_3025891 : Nat := 118140960795 + 3025891 * 2 ^ 59
def prefixEnd_3025891 : Nat := 4983230072969 + 3 ^ 40 * 3025891 * 2
def baseEnd_3025891 : Nat := 1035824327409283947497791

theorem tailTrace_3025891 : CollatzResearch.WordTrace tailWord_3025891 prefixEnd_3025891 1035824327409283947497791 := by
  unfold tailWord_3025891
  simp only [CollatzResearch.WordTrace]
  refine ⟨110363311480721162884869527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73575540987147441923246351 110363311480721162884869527)
  ·
    refine ⟨165544967221081744327304291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110363311480721162884869527 165544967221081744327304291)
    ·
      refine ⟨248317450831622616490956437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165544967221081744327304291 248317450831622616490956437)
      ·
        refine ⟨11639880507732310148013583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248317450831622616490956437 11639880507732310148013583)
        ·
          refine ⟨17459820761598465222020375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639880507732310148013583 17459820761598465222020375)
          ·
            refine ⟨26189731142397697833030563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17459820761598465222020375 26189731142397697833030563)
            ·
              refine ⟨39284596713596546749545845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26189731142397697833030563 39284596713596546749545845)
              ·
                refine ⟨3682930941899676257769923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39284596713596546749545845 3682930941899676257769923)
                ·
                  refine ⟨5524396412849514386654885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682930941899676257769923 5524396412849514386654885)
                  ·
                    refine ⟨1035824327409283947497791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524396412849514386654885 1035824327409283947497791)
                    ·
                      rfl

theorem cell22_3025891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_3025891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025891 prefixEnd_3025891 := by exact prefixLift 3025891
  have htrace : WordTrace (prefixWord ++ tailWord_3025891) baseStart_3025891 baseEnd_3025891 := by
    simpa [prefixWord, tailWord_3025891, baseEnd_3025891] using wordTrace_append hprefix tailTrace_3025891
  have hstable : (prefixWord ++ tailWord_3025891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025891).length < 2 ^ (prefixWord ++ tailWord_3025891).sum := by decide
  have hdescent : baseEnd_3025891 < baseStart_3025891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025964 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_3025964 : Nat := 118140960795 + 3025964 * 2 ^ 59
def prefixEnd_3025964 : Nat := 4983230072969 + 3 ^ 40 * 3025964 * 2
def baseEnd_3025964 : Nat := 1035849316801136090422567

theorem tailTrace_3025964 : CollatzResearch.WordTrace tailWord_3025964 prefixEnd_3025964 1035849316801136090422567 := by
  unfold tailWord_3025964
  simp only [CollatzResearch.WordTrace]
  refine ⟨55182987004728348176138473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73577316006304464234851297 55182987004728348176138473)
  ·
    refine ⟨41387240253546261132103855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55182987004728348176138473 41387240253546261132103855)
    ·
      refine ⟨62080860380319391698155783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41387240253546261132103855 62080860380319391698155783)
      ·
        refine ⟨93121290570479087547233675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62080860380319391698155783 93121290570479087547233675)
        ·
          refine ⟨139681935855718631320850513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93121290570479087547233675 139681935855718631320850513)
          ·
            refine ⟨104761451891788973490637885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139681935855718631320850513 104761451891788973490637885)
            ·
              refine ⟨39285544459420865058989207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104761451891788973490637885 39285544459420865058989207)
              ·
                refine ⟨58928316689131297588483811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39285544459420865058989207 58928316689131297588483811)
                ·
                  refine ⟨88392475033696946382725717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58928316689131297588483811 88392475033696946382725717)
                  ·
                    refine ⟨1035849316801136090422567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88392475033696946382725717 1035849316801136090422567)
                    ·
                      rfl

theorem cell22_3025964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_3025964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3025964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3025964 prefixEnd_3025964 := by exact prefixLift 3025964
  have htrace : WordTrace (prefixWord ++ tailWord_3025964) baseStart_3025964 baseEnd_3025964 := by
    simpa [prefixWord, tailWord_3025964, baseEnd_3025964] using wordTrace_append hprefix tailTrace_3025964
  have hstable : (prefixWord ++ tailWord_3025964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025964).length < 2 ^ (prefixWord ++ tailWord_3025964).sum := by decide
  have hdescent : baseEnd_3025964 < baseStart_3025964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026006 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3026006 : Nat := 118140960795 + 3026006 * 2 ^ 59
def prefixEnd_3026006 : Nat := 4983230072969 + 3 ^ 40 * 3026006 * 2
def baseEnd_3026006 : Nat := 1035863694259461980872439

theorem tailTrace_3026006 : CollatzResearch.WordTrace tailWord_3026006 prefixEnd_3026006 1035863694259461980872439 := by
  unfold tailWord_3026006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897969117206533595331617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73578337250203025016870581 6897969117206533595331617)
  ·
    refine ⟨5173476837904900196498713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6897969117206533595331617 5173476837904900196498713)
    ·
      refine ⟨3880107628428675147374035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5173476837904900196498713 3880107628428675147374035)
      ·
        refine ⟨5820161442643012721061053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880107628428675147374035 5820161442643012721061053)
        ·
          refine ⟨2182560540991129770397895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5820161442643012721061053 2182560540991129770397895)
          ·
            refine ⟨3273840811486694655596843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182560540991129770397895 3273840811486694655596843)
            ·
              refine ⟨4910761217230041983395265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273840811486694655596843 4910761217230041983395265)
              ·
                refine ⟨3683070912922531487546449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910761217230041983395265 3683070912922531487546449)
                ·
                  refine ⟨2762303184691898615659837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683070912922531487546449 2762303184691898615659837)
                  ·
                    refine ⟨1035863694259461980872439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762303184691898615659837 1035863694259461980872439)
                    ·
                      rfl

theorem cell22_3026006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3026006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026006 prefixEnd_3026006 := by exact prefixLift 3026006
  have htrace : WordTrace (prefixWord ++ tailWord_3026006) baseStart_3026006 baseEnd_3026006 := by
    simpa [prefixWord, tailWord_3026006, baseEnd_3026006] using wordTrace_append hprefix tailTrace_3026006
  have hstable : (prefixWord ++ tailWord_3026006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026006).length < 2 ^ (prefixWord ++ tailWord_3026006).sum := by decide
  have hdescent : baseEnd_3026006 < baseStart_3026006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026030 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3026030 : Nat := 118140960795 + 3026030 * 2 ^ 59
def prefixEnd_3026030 : Nat := 4983230072969 + 3 ^ 40 * 3026030 * 2
def baseEnd_3026030 : Nat := 345290636649977972757455

theorem tailTrace_3026030 : CollatzResearch.WordTrace tailWord_3026030 prefixEnd_3026030 345290636649977972757455 := by
  unfold tailWord_3026030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796047653402198703022443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73578920818145059749453029 13796047653402198703022443)
  ·
    refine ⟨20694071480103298054533665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13796047653402198703022443 20694071480103298054533665)
    ·
      refine ⟨15520553610077473540900249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20694071480103298054533665 15520553610077473540900249)
      ·
        refine ⟨11640415207558105155675187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15520553610077473540900249 11640415207558105155675187)
        ·
          refine ⟨17460622811337157733512781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640415207558105155675187 17460622811337157733512781)
          ·
            refine ⟨6547733554251434150067293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17460622811337157733512781 6547733554251434150067293)
            ·
              refine ⟨2455400082844287806275235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6547733554251434150067293 2455400082844287806275235)
              ·
                refine ⟨3683100124266431709412853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455400082844287806275235 3683100124266431709412853)
                ·
                  refine ⟨345290636649977972757455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683100124266431709412853 345290636649977972757455)
                  ·
                    rfl

theorem cell22_3026030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3026030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026030 prefixEnd_3026030 := by exact prefixLift 3026030
  have htrace : WordTrace (prefixWord ++ tailWord_3026030) baseStart_3026030 baseEnd_3026030 := by
    simpa [prefixWord, tailWord_3026030, baseEnd_3026030] using wordTrace_append hprefix tailTrace_3026030
  have hstable : (prefixWord ++ tailWord_3026030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026030).length < 2 ^ (prefixWord ++ tailWord_3026030).sum := by decide
  have hdescent : baseEnd_3026030 < baseStart_3026030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026133 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3026133 : Nat := 118140960795 + 3026133 * 2 ^ 59
def prefixEnd_3026133 : Nat := 4983230072969 + 3 ^ 40 * 3026133 * 2
def baseEnd_3026133 : Nat := 1035907168954875982947049

theorem tailTrace_3026133 : CollatzResearch.WordTrace tailWord_3026133 prefixEnd_3026133 1035907168954875982947049 := by
  unfold tailWord_3026133
  simp only [CollatzResearch.WordTrace]
  refine ⟨110372137945844438215179053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73581425297229625476786035 110372137945844438215179053)
  ·
    refine ⟨41389551729691664330692145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110372137945844438215179053 41389551729691664330692145)
    ·
      refine ⟨31042163797268748248019109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41389551729691664330692145 31042163797268748248019109)
      ·
        refine ⟨5820405711987890296503583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31042163797268748248019109 5820405711987890296503583)
        ·
          refine ⟨8730608567981835444755375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820405711987890296503583 8730608567981835444755375)
          ·
            refine ⟨13095912851972753167133063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730608567981835444755375 13095912851972753167133063)
            ·
              refine ⟨19643869277959129750699595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13095912851972753167133063 19643869277959129750699595)
              ·
                refine ⟨29465803916938694626049393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19643869277959129750699595 29465803916938694626049393)
                ·
                  refine ⟨22099352937704020969537045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29465803916938694626049393 22099352937704020969537045)
                  ·
                    refine ⟨1035907168954875982947049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22099352937704020969537045 1035907168954875982947049)
                    ·
                      rfl

theorem cell22_3026133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3026133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026133 prefixEnd_3026133 := by exact prefixLift 3026133
  have htrace : WordTrace (prefixWord ++ tailWord_3026133) baseStart_3026133 baseEnd_3026133 := by
    simpa [prefixWord, tailWord_3026133, baseEnd_3026133] using wordTrace_append hprefix tailTrace_3026133
  have hstable : (prefixWord ++ tailWord_3026133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026133).length < 2 ^ (prefixWord ++ tailWord_3026133).sum := by decide
  have hdescent : baseEnd_3026133 < baseStart_3026133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026148 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_3026148 : Nat := 118140960795 + 3026148 * 2 ^ 59
def prefixEnd_3026148 : Nat := 4983230072969 + 3 ^ 40 * 3026148 * 2
def baseEnd_3026148 : Nat := 345304101253806981274001

theorem tailTrace_3026148 : CollatzResearch.WordTrace tailWord_3026148 prefixEnd_3026148 345304101253806981274001 := by
  unfold tailWord_3026148
  simp only [CollatzResearch.WordTrace]
  refine ⟨55186342520395047888487549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73581790027193397184650065 55186342520395047888487549)
  ·
    refine ⟨20694878445148142958182831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55186342520395047888487549 20694878445148142958182831)
    ·
      refine ⟨31042317667722214437274247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20694878445148142958182831 31042317667722214437274247)
      ·
        refine ⟨46563476501583321655911371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31042317667722214437274247 46563476501583321655911371)
        ·
          refine ⟨69845214752374982483867057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46563476501583321655911371 69845214752374982483867057)
          ·
            refine ⟨52383911064281236862900293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69845214752374982483867057 52383911064281236862900293)
            ·
              refine ⟨9821983324552731911793805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52383911064281236862900293 9821983324552731911793805)
              ·
                refine ⟨3683243746707274466922677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821983324552731911793805 3683243746707274466922677)
                ·
                  refine ⟨345304101253806981274001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683243746707274466922677 345304101253806981274001)
                  ·
                    rfl

theorem cell22_3026148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_3026148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026148 prefixEnd_3026148 := by exact prefixLift 3026148
  have htrace : WordTrace (prefixWord ++ tailWord_3026148) baseStart_3026148 baseEnd_3026148 := by
    simpa [prefixWord, tailWord_3026148, baseEnd_3026148] using wordTrace_append hprefix tailTrace_3026148
  have hstable : (prefixWord ++ tailWord_3026148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026148).length < 2 ^ (prefixWord ++ tailWord_3026148).sum := by decide
  have hdescent : baseEnd_3026148 < baseStart_3026148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026176 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_3026176 : Nat := 118140960795 + 3026176 * 2 ^ 59
def prefixEnd_3026176 : Nat := 4983230072969 + 3 ^ 40 * 3026176 * 2
def baseEnd_3026176 : Nat := 345307296244546068040639

theorem tailTrace_3026176 : CollatzResearch.WordTrace tailWord_3026176 prefixEnd_3026176 345307296244546068040639 := by
  unfold tailWord_3026176
  simp only [CollatzResearch.WordTrace]
  refine ⟨55186853142344328279497191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73582470856459104372662921 55186853142344328279497191)
  ·
    refine ⟨82780279713516492419245787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55186853142344328279497191 82780279713516492419245787)
    ·
      refine ⟨124170419570274738628868681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82780279713516492419245787 124170419570274738628868681)
      ·
        refine ⟨93127814677706053971651511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124170419570274738628868681 93127814677706053971651511)
        ·
          refine ⟨139691722016559080957477267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93127814677706053971651511 139691722016559080957477267)
          ·
            refine ⟨209537583024838621436215901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139691722016559080957477267 209537583024838621436215901)
            ·
              refine ⟨78576593634314483038580963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209537583024838621436215901 78576593634314483038580963)
              ·
                refine ⟨117864890451471724557871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78576593634314483038580963 117864890451471724557871445)
                ·
                  refine ⟨345307296244546068040639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117864890451471724557871445 345307296244546068040639)
                  ·
                    rfl

theorem cell22_3026176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_3026176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026176 prefixEnd_3026176 := by exact prefixLift 3026176
  have htrace : WordTrace (prefixWord ++ tailWord_3026176) baseStart_3026176 baseEnd_3026176 := by
    simpa [prefixWord, tailWord_3026176, baseEnd_3026176] using wordTrace_append hprefix tailTrace_3026176
  have hstable : (prefixWord ++ tailWord_3026176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026176).length < 2 ^ (prefixWord ++ tailWord_3026176).sum := by decide
  have hdescent : baseEnd_3026176 < baseStart_3026176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026191 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3026191 : Nat := 118140960795 + 3026191 * 2 ^ 59
def prefixEnd_3026191 : Nat := 4983230072969 + 3 ^ 40 * 3026191 * 2
def baseEnd_3026191 : Nat := 1035927023540183164996871

theorem tailTrace_3026191 : CollatzResearch.WordTrace tailWord_3026191 prefixEnd_3026191 1035927023540183164996871 := by
  unfold tailWord_3026191
  simp only [CollatzResearch.WordTrace]
  refine ⟨110374253379634314120790427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73582835586422876080526951 110374253379634314120790427)
  ·
    refine ⟨165561380069451471181185641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110374253379634314120790427 165561380069451471181185641)
    ·
      refine ⟨124171035052088603385889231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165561380069451471181185641 124171035052088603385889231)
      ·
        refine ⟨186256552578132905078833847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124171035052088603385889231 186256552578132905078833847)
        ·
          refine ⟨279384828867199357618250771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186256552578132905078833847 279384828867199357618250771)
          ·
            refine ⟨419077243300799036427376157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279384828867199357618250771 419077243300799036427376157)
            ·
              refine ⟨157153966237799638660266059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419077243300799036427376157 157153966237799638660266059)
              ·
                refine ⟨235730949356699457990399089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157153966237799638660266059 235730949356699457990399089)
                ·
                  refine ⟨176798212017524593492799317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235730949356699457990399089 176798212017524593492799317)
                  ·
                    refine ⟨1035927023540183164996871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176798212017524593492799317 1035927023540183164996871)
                    ·
                      rfl

theorem cell22_3026191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3026191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026191 prefixEnd_3026191 := by exact prefixLift 3026191
  have htrace : WordTrace (prefixWord ++ tailWord_3026191) baseStart_3026191 baseEnd_3026191 := by
    simpa [prefixWord, tailWord_3026191, baseEnd_3026191] using wordTrace_append hprefix tailTrace_3026191
  have hstable : (prefixWord ++ tailWord_3026191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026191).length < 2 ^ (prefixWord ++ tailWord_3026191).sum := by decide
  have hdescent : baseEnd_3026191 < baseStart_3026191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026193 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 6]
def baseStart_3026193 : Nat := 118140960795 + 3026193 * 2 ^ 59
def prefixEnd_3026193 : Nat := 4983230072969 + 3 ^ 40 * 3026193 * 2
def baseEnd_3026193 : Nat := 345309236060351942148955

theorem tailTrace_3026193 : CollatzResearch.WordTrace tailWord_3026193 prefixEnd_3026193 345309236060351942148955 := by
  unfold tailWord_3026193
  simp only [CollatzResearch.WordTrace]
  refine ⟨110374326325627068462363233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73582884217084712308242155 110374326325627068462363233)
  ·
    refine ⟨82780744744220301346772425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110374326325627068462363233 82780744744220301346772425)
    ·
      refine ⟨62085558558165226010079319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82780744744220301346772425 62085558558165226010079319)
      ·
        refine ⟨93128337837247839015118979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62085558558165226010079319 93128337837247839015118979)
        ·
          refine ⟨139692506755871758522678469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93128337837247839015118979 139692506755871758522678469)
          ·
            refine ⟨26192345016725954723002213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139692506755871758522678469 26192345016725954723002213)
            ·
              refine ⟨4911064690636116510562915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26192345016725954723002213 4911064690636116510562915)
              ·
                refine ⟨7366597035954174765844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4911064690636116510562915 7366597035954174765844373)
                ·
                  refine ⟨345309236060351942148955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7366597035954174765844373 345309236060351942148955)
                  ·
                    rfl

theorem cell22_3026193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_3026193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026193 prefixEnd_3026193 := by exact prefixLift 3026193
  have htrace : WordTrace (prefixWord ++ tailWord_3026193) baseStart_3026193 baseEnd_3026193 := by
    simpa [prefixWord, tailWord_3026193, baseEnd_3026193] using wordTrace_append hprefix tailTrace_3026193
  have hstable : (prefixWord ++ tailWord_3026193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026193).length < 2 ^ (prefixWord ++ tailWord_3026193).sum := by decide
  have hdescent : baseEnd_3026193 < baseStart_3026193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026223 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_3026223 : Nat := 118140960795 + 3026223 * 2 ^ 59
def prefixEnd_3026223 : Nat := 4983230072969 + 3 ^ 40 * 3026223 * 2
def baseEnd_3026223 : Nat := 1035937977794145748196773

theorem tailTrace_3026223 : CollatzResearch.WordTrace tailWord_3026223 prefixEnd_3026223 1035937977794145748196773 := by
  unfold tailWord_3026223
  simp only [CollatzResearch.WordTrace]
  refine ⟨110375420515518383585955323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73583613677012255723970215 110375420515518383585955323)
  ·
    refine ⟨165563130773277575378932985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110375420515518383585955323 165563130773277575378932985)
    ·
      refine ⟨124172348079958181534199739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165563130773277575378932985 124172348079958181534199739)
      ·
        refine ⟨186258522119937272301299609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124172348079958181534199739 186258522119937272301299609)
        ·
          refine ⟨139693891589952954225974707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186258522119937272301299609 139693891589952954225974707)
          ·
            refine ⟨209540837384929431338962061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139693891589952954225974707 209540837384929431338962061)
            ·
              refine ⟨78577814019348536752110773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209540837384929431338962061 78577814019348536752110773)
              ·
                refine ⟨7366670064313925320510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78577814019348536752110773 7366670064313925320510385)
                ·
                  refine ⟨5525002548235443990382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7366670064313925320510385 5525002548235443990382789)
                  ·
                    refine ⟨1035937977794145748196773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525002548235443990382789 1035937977794145748196773)
                    ·
                      rfl

theorem cell22_3026223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_3026223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026223 prefixEnd_3026223 := by exact prefixLift 3026223
  have htrace : WordTrace (prefixWord ++ tailWord_3026223) baseStart_3026223 baseEnd_3026223 := by
    simpa [prefixWord, tailWord_3026223, baseEnd_3026223] using wordTrace_append hprefix tailTrace_3026223
  have hstable : (prefixWord ++ tailWord_3026223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026223).length < 2 ^ (prefixWord ++ tailWord_3026223).sum := by decide
  have hdescent : baseEnd_3026223 < baseStart_3026223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026225 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_3026225 : Nat := 118140960795 + 3026225 * 2 ^ 59
def prefixEnd_3026225 : Nat := 4983230072969 + 3 ^ 40 * 3026225 * 2
def baseEnd_3026225 : Nat := 1035938662435018409646767

theorem tailTrace_3026225 : CollatzResearch.WordTrace tailWord_3026225 prefixEnd_3026225 1035938662435018409646767 := by
  unfold tailWord_3026225
  simp only [CollatzResearch.WordTrace]
  refine ⟨110375493461511137927528129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73583662307674091951685419 110375493461511137927528129)
  ·
    refine ⟨82781620096133353445646097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110375493461511137927528129 82781620096133353445646097)
    ·
      refine ⟨62086215072100015084234573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82781620096133353445646097 62086215072100015084234573)
      ·
        refine ⟨23282330652037505656587965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62086215072100015084234573 23282330652037505656587965)
        ·
          refine ⟨8730873994514064621220487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23282330652037505656587965 8730873994514064621220487)
          ·
            refine ⟨13096310991771096931830731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730873994514064621220487 13096310991771096931830731)
            ·
              refine ⟨19644466487656645397746097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096310991771096931830731 19644466487656645397746097)
              ·
                refine ⟨14733349865742484048309573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19644466487656645397746097 14733349865742484048309573)
                ·
                  refine ⟨2762503099826715759058045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14733349865742484048309573 2762503099826715759058045)
                  ·
                    refine ⟨1035938662435018409646767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762503099826715759058045 1035938662435018409646767)
                    ·
                      rfl

theorem cell22_3026225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_3026225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026225 prefixEnd_3026225 := by exact prefixLift 3026225
  have htrace : WordTrace (prefixWord ++ tailWord_3026225) baseStart_3026225 baseEnd_3026225 := by
    simpa [prefixWord, tailWord_3026225, baseEnd_3026225] using wordTrace_append hprefix tailTrace_3026225
  have hstable : (prefixWord ++ tailWord_3026225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026225).length < 2 ^ (prefixWord ++ tailWord_3026225).sum := by decide
  have hdescent : baseEnd_3026225 < baseStart_3026225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026227 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 4]
def baseStart_3026227 : Nat := 118140960795 + 3026227 * 2 ^ 59
def prefixEnd_3026227 : Nat := 4983230072969 + 3 ^ 40 * 3026227 * 2
def baseEnd_3026227 : Nat := 345313115691963690365587

theorem tailTrace_3026227 : CollatzResearch.WordTrace tailWord_3026227 prefixEnd_3026227 345313115691963690365587 := by
  unfold tailWord_3026227
  simp only [CollatzResearch.WordTrace]
  refine ⟨110375566407503892269100935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73583710938335928179400623 110375566407503892269100935)
  ·
    refine ⟨165563349611255838403651403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110375566407503892269100935 165563349611255838403651403)
    ·
      refine ⟨248345024416883757605477105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165563349611255838403651403 248345024416883757605477105)
      ·
        refine ⟨186258768312662818204107829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248345024416883757605477105 186258768312662818204107829)
        ·
          refine ⟨17461759529312139206635109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186258768312662818204107829 17461759529312139206635109)
          ·
            refine ⟨3274079911746026101244083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17461759529312139206635109 3274079911746026101244083)
            ·
              refine ⟨4911119867619039151866125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274079911746026101244083 4911119867619039151866125)
              ·
                refine ⟨1841669950357139681949797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4911119867619039151866125 1841669950357139681949797)
                ·
                  refine ⟨345313115691963690365587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841669950357139681949797 345313115691963690365587)
                  ·
                    rfl

theorem cell22_3026227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 4].length) (baseStart_3026227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026227 prefixEnd_3026227 := by exact prefixLift 3026227
  have htrace : WordTrace (prefixWord ++ tailWord_3026227) baseStart_3026227 baseEnd_3026227 := by
    simpa [prefixWord, tailWord_3026227, baseEnd_3026227] using wordTrace_append hprefix tailTrace_3026227
  have hstable : (prefixWord ++ tailWord_3026227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026227).length < 2 ^ (prefixWord ++ tailWord_3026227).sum := by decide
  have hdescent : baseEnd_3026227 < baseStart_3026227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026287 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 1, 3]
def baseStart_3026287 : Nat := 118140960795 + 3026287 * 2 ^ 59
def prefixEnd_3026287 : Nat := 4983230072969 + 3 ^ 40 * 3026287 * 2
def baseEnd_3026287 : Nat := 1035959886302070914596577

theorem tailTrace_3026287 : CollatzResearch.WordTrace tailWord_3026287 prefixEnd_3026287 1035959886302070914596577 := by
  unfold tailWord_3026287
  simp only [CollatzResearch.WordTrace]
  refine ⟨110377754787286522516285115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73585169858191015010856743 110377754787286522516285115)
  ·
    refine ⟨165566632180929783774427673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110377754787286522516285115 165566632180929783774427673)
    ·
      refine ⟨124174974135697337830820755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165566632180929783774427673 124174974135697337830820755)
      ·
        refine ⟨186262461203546006746231133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124174974135697337830820755 186262461203546006746231133)
        ·
          refine ⟨69848422951329752529836675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186262461203546006746231133 69848422951329752529836675)
          ·
            refine ⟨104772634426994628794755013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69848422951329752529836675 104772634426994628794755013)
            ·
              refine ⟨19644868955061492899016565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104772634426994628794755013 19644868955061492899016565)
              ·
                refine ⟨1841706464537014959282803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19644868955061492899016565 1841706464537014959282803)
                ·
                  refine ⟨2762559696805522438924205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841706464537014959282803 2762559696805522438924205)
                  ·
                    refine ⟨1035959886302070914596577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762559696805522438924205 1035959886302070914596577)
                    ·
                      rfl

theorem cell22_3026287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_3026287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026287 prefixEnd_3026287 := by exact prefixLift 3026287
  have htrace : WordTrace (prefixWord ++ tailWord_3026287) baseStart_3026287 baseEnd_3026287 := by
    simpa [prefixWord, tailWord_3026287, baseEnd_3026287] using wordTrace_append hprefix tailTrace_3026287
  have hstable : (prefixWord ++ tailWord_3026287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026287).length < 2 ^ (prefixWord ++ tailWord_3026287).sum := by decide
  have hdescent : baseEnd_3026287 < baseStart_3026287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026298 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_3026298 : Nat := 118140960795 + 3026298 * 2 ^ 59
def prefixEnd_3026298 : Nat := 4983230072969 + 3 ^ 40 * 3026298 * 2
def baseEnd_3026298 : Nat := 1035963651826870552571543

theorem tailTrace_3026298 : CollatzResearch.WordTrace tailWord_3026298 prefixEnd_3026298 1035963651826870552571543 := by
  unfold tailWord_3026298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27594538997561667848733887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73585437326831114263290365 27594538997561667848733887)
  ·
    refine ⟨41391808496342501773100831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27594538997561667848733887 41391808496342501773100831)
    ·
      refine ⟨62087712744513752659651247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41391808496342501773100831 62087712744513752659651247)
      ·
        refine ⟨93131569116770628989476871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62087712744513752659651247 93131569116770628989476871)
        ·
          refine ⟨139697353675155943484215307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93131569116770628989476871 139697353675155943484215307)
          ·
            refine ⟨209546030512733915226322961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139697353675155943484215307 209546030512733915226322961)
            ·
              refine ⟨157159522884550436419742221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209546030512733915226322961 157159522884550436419742221)
              ·
                refine ⟨58934821081706413657403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157159522884550436419742221 58934821081706413657403333)
                ·
                  refine ⟨11050278952819952560763125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58934821081706413657403333 11050278952819952560763125)
                  ·
                    refine ⟨1035963651826870552571543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11050278952819952560763125 1035963651826870552571543)
                    ·
                      rfl

theorem cell22_3026298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_3026298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026298 prefixEnd_3026298 := by exact prefixLift 3026298
  have htrace : WordTrace (prefixWord ++ tailWord_3026298) baseStart_3026298 baseEnd_3026298 := by
    simpa [prefixWord, tailWord_3026298, baseEnd_3026298] using wordTrace_append hprefix tailTrace_3026298
  have hstable : (prefixWord ++ tailWord_3026298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026298).length < 2 ^ (prefixWord ++ tailWord_3026298).sum := by decide
  have hdescent : baseEnd_3026298 < baseStart_3026298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026300 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_3026300 : Nat := 118140960795 + 3026300 * 2 ^ 59
def prefixEnd_3026300 : Nat := 4983230072969 + 3 ^ 40 * 3026300 * 2
def baseEnd_3026300 : Nat := 345321445489247738007179

theorem tailTrace_3026300 : CollatzResearch.WordTrace tailWord_3026300 prefixEnd_3026300 345321445489247738007179 := by
  unfold tailWord_3026300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55189114468119712868254177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73585485957492950491005569 55189114468119712868254177)
  ·
    refine ⟨41391835851089784651190633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55189114468119712868254177 41391835851089784651190633)
    ·
      refine ⟨31043876888317338488392975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41391835851089784651190633 31043876888317338488392975)
      ·
        refine ⟨46565815332476007732589463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31043876888317338488392975 46565815332476007732589463)
        ·
          refine ⟨69848722998714011598884195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46565815332476007732589463 69848722998714011598884195)
          ·
            refine ⟨104773084498071017398326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69848722998714011598884195 104773084498071017398326293)
            ·
              refine ⟨4911238335847078940546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104773084498071017398326293 4911238335847078940546545)
              ·
                refine ⟨3683428751885309205409909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4911238335847078940546545 3683428751885309205409909)
                ·
                  refine ⟨345321445489247738007179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683428751885309205409909 345321445489247738007179)
                  ·
                    rfl

theorem cell22_3026300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_3026300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026300 prefixEnd_3026300 := by exact prefixLift 3026300
  have htrace : WordTrace (prefixWord ++ tailWord_3026300) baseStart_3026300 baseEnd_3026300 := by
    simpa [prefixWord, tailWord_3026300, baseEnd_3026300] using wordTrace_append hprefix tailTrace_3026300
  have hstable : (prefixWord ++ tailWord_3026300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026300).length < 2 ^ (prefixWord ++ tailWord_3026300).sum := by decide
  have hdescent : baseEnd_3026300 < baseStart_3026300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026330 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_3026330 : Nat := 118140960795 + 3026330 * 2 ^ 59
def prefixEnd_3026330 : Nat := 4983230072969 + 3 ^ 40 * 3026330 * 2
def baseEnd_3026330 : Nat := 1035974606080833135771445

theorem tailTrace_3026330 : CollatzResearch.WordTrace tailWord_3026330 prefixEnd_3026330 1035974606080833135771445 := by
  unfold tailWord_3026330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27594830781532685215025111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73586215417420493906733629 27594830781532685215025111)
  ·
    refine ⟨41392246172299027822537667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27594830781532685215025111 41392246172299027822537667)
    ·
      refine ⟨62088369258448541733806501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41392246172299027822537667 62088369258448541733806501)
      ·
        refine ⟨11641569235959101575088719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62088369258448541733806501 11641569235959101575088719)
        ·
          refine ⟨17462353853938652362633079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11641569235959101575088719 17462353853938652362633079)
          ·
            refine ⟨26193530780907978543949619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17462353853938652362633079 26193530780907978543949619)
            ·
              refine ⟨39290296171361967815924429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26193530780907978543949619 39290296171361967815924429)
              ·
                refine ⟨14733861064260737930971661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39290296171361967815924429 14733861064260737930971661)
                ·
                  refine ⟨5525197899097776724114373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14733861064260737930971661 5525197899097776724114373)
                  ·
                    refine ⟨1035974606080833135771445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525197899097776724114373 1035974606080833135771445)
                    ·
                      rfl

theorem cell22_3026330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_3026330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026330 prefixEnd_3026330 := by exact prefixLift 3026330
  have htrace : WordTrace (prefixWord ++ tailWord_3026330) baseStart_3026330 baseEnd_3026330 := by
    simpa [prefixWord, tailWord_3026330, baseEnd_3026330] using wordTrace_append hprefix tailTrace_3026330
  have hstable : (prefixWord ++ tailWord_3026330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026330).length < 2 ^ (prefixWord ++ tailWord_3026330).sum := by decide
  have hdescent : baseEnd_3026330 < baseStart_3026330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026480 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_3026480 : Nat := 118140960795 + 3026480 * 2 ^ 59
def prefixEnd_3026480 : Nat := 4983230072969 + 3 ^ 40 * 3026480 * 2
def baseEnd_3026480 : Nat := 345341984715427581506995

theorem tailTrace_3026480 : CollatzResearch.WordTrace tailWord_3026480 prefixEnd_3026480 345341984715427581506995 := by
  unfold tailWord_3026480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55192397037793658239030447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73589862717058210985373929 55192397037793658239030447)
  ·
    refine ⟨82788595556690487358545671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55192397037793658239030447 82788595556690487358545671)
    ·
      refine ⟨124182893335035731037818507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82788595556690487358545671 124182893335035731037818507)
      ·
        refine ⟨186274340002553596556727761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124182893335035731037818507 186274340002553596556727761)
        ·
          refine ⟨139705755001915197417545821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186274340002553596556727761 139705755001915197417545821)
          ·
            refine ⟨52389658125718199031579683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139705755001915197417545821 52389658125718199031579683)
            ·
              refine ⟨78584487188577298547369525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52389658125718199031579683 78584487188577298547369525)
              ·
                refine ⟨7367295673929121738815893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78584487188577298547369525 7367295673929121738815893)
                ·
                  refine ⟨345341984715427581506995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7367295673929121738815893 345341984715427581506995)
                  ·
                    rfl

theorem cell22_3026480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_3026480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026480 prefixEnd_3026480 := by exact prefixLift 3026480
  have htrace : WordTrace (prefixWord ++ tailWord_3026480) baseStart_3026480 baseEnd_3026480 := by
    simpa [prefixWord, tailWord_3026480, baseEnd_3026480] using wordTrace_append hprefix tailTrace_3026480
  have hstable : (prefixWord ++ tailWord_3026480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026480).length < 2 ^ (prefixWord ++ tailWord_3026480).sum := by decide
  have hdescent : baseEnd_3026480 < baseStart_3026480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026497 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 6]
def baseStart_3026497 : Nat := 118140960795 + 3026497 * 2 ^ 59
def prefixEnd_3026497 : Nat := 4983230072969 + 3 ^ 40 * 3026497 * 2
def baseEnd_3026497 : Nat := 345343924531233455615311

theorem tailTrace_3026497 : CollatzResearch.WordTrace tailWord_3026497 prefixEnd_3026497 345343924531233455615311 := by
  unfold tailWord_3026497
  simp only [CollatzResearch.WordTrace]
  refine ⟨110385414116525728381429745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73590276077683818920953163 110385414116525728381429745)
  ·
    refine ⟨82789060587394296286072309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110385414116525728381429745 82789060587394296286072309)
    ·
      refine ⟨7761474430068215276819279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82789060587394296286072309 7761474430068215276819279)
      ·
        refine ⟨11642211645102322915228919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761474430068215276819279 11642211645102322915228919)
        ·
          refine ⟨17463317467653484372843379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642211645102322915228919 17463317467653484372843379)
          ·
            refine ⟨26194976201480226559265069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17463317467653484372843379 26194976201480226559265069)
            ·
              refine ⟨9823116075555084959724401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26194976201480226559265069 9823116075555084959724401)
              ·
                refine ⟨7367337056666313719793301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9823116075555084959724401 7367337056666313719793301)
                ·
                  refine ⟨345343924531233455615311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7367337056666313719793301 345343924531233455615311)
                  ·
                    rfl

theorem cell22_3026497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_3026497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026497 prefixEnd_3026497 := by exact prefixLift 3026497
  have htrace : WordTrace (prefixWord ++ tailWord_3026497) baseStart_3026497 baseEnd_3026497 := by
    simpa [prefixWord, tailWord_3026497, baseEnd_3026497] using wordTrace_append hprefix tailTrace_3026497
  have hstable : (prefixWord ++ tailWord_3026497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026497).length < 2 ^ (prefixWord ++ tailWord_3026497).sum := by decide
  have hdescent : baseEnd_3026497 < baseStart_3026497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026512 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_3026512 : Nat := 118140960795 + 3026512 * 2 ^ 59
def prefixEnd_3026512 : Nat := 4983230072969 + 3 ^ 40 * 3026512 * 2
def baseEnd_3026512 : Nat := 1036036908400245327720887

theorem tailTrace_3026512 : CollatzResearch.WordTrace tailWord_3026512 prefixEnd_3026512 1036036908400245327720887 := by
  unfold tailWord_3026512
  simp only [CollatzResearch.WordTrace]
  refine ⟨55192980605735692971612895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73590640807647590628817193 55192980605735692971612895)
  ·
    refine ⟨82789470908603539457419343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55192980605735692971612895 82789470908603539457419343)
    ·
      refine ⟨124184206362905309186129015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82789470908603539457419343 124184206362905309186129015)
      ·
        refine ⟨186276309544357963779193523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124184206362905309186129015 186276309544357963779193523)
        ·
          refine ⟨279414464316536945668790285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186276309544357963779193523 279414464316536945668790285)
          ·
            refine ⟨104780424118701354625796357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279414464316536945668790285 104780424118701354625796357)
            ·
              refine ⟨19646329522256503992336817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104780424118701354625796357 19646329522256503992336817)
              ·
                refine ⟨14734747141692377994252613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19646329522256503992336817 14734747141692377994252613)
                ·
                  refine ⟨2762765089067320873922365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14734747141692377994252613 2762765089067320873922365)
                  ·
                    refine ⟨1036036908400245327720887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762765089067320873922365 1036036908400245327720887)
                    ·
                      rfl

theorem cell22_3026512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_3026512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026512 prefixEnd_3026512 := by exact prefixLift 3026512
  have htrace : WordTrace (prefixWord ++ tailWord_3026512) baseStart_3026512 baseEnd_3026512 := by
    simpa [prefixWord, tailWord_3026512, baseEnd_3026512] using wordTrace_append hprefix tailTrace_3026512
  have hstable : (prefixWord ++ tailWord_3026512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026512).length < 2 ^ (prefixWord ++ tailWord_3026512).sum := by decide
  have hdescent : baseEnd_3026512 < baseStart_3026512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026514 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_3026514 : Nat := 118140960795 + 3026514 * 2 ^ 59
def prefixEnd_3026514 : Nat := 4983230072969 + 3 ^ 40 * 3026514 * 2
def baseEnd_3026514 : Nat := 345345864347039329723627

theorem tailTrace_3026514 : CollatzResearch.WordTrace tailWord_3026514 prefixEnd_3026514 345345864347039329723627 := by
  unfold tailWord_3026514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596508539366035071199649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73590689438309426856532397 27596508539366035071199649)
  ·
    refine ⟨20697381404524526303399737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27596508539366035071199649 20697381404524526303399737)
    ·
      refine ⟨15523036053393394727549803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20697381404524526303399737 15523036053393394727549803)
      ·
        refine ⟨23284554080090092091324705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15523036053393394727549803 23284554080090092091324705)
        ·
          refine ⟨17463415560067569068493529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23284554080090092091324705 17463415560067569068493529)
          ·
            refine ⟨13097561670050676801370147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17463415560067569068493529 13097561670050676801370147)
            ·
              refine ⟨19646342505076015202055221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097561670050676801370147 19646342505076015202055221)
              ·
                refine ⟨1841844609850876425192677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19646342505076015202055221 1841844609850876425192677)
                ·
                  refine ⟨345345864347039329723627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841844609850876425192677 345345864347039329723627)
                  ·
                    rfl

theorem cell22_3026514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_3026514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026514 prefixEnd_3026514 := by exact prefixLift 3026514
  have htrace : WordTrace (prefixWord ++ tailWord_3026514) baseStart_3026514 baseEnd_3026514 := by
    simpa [prefixWord, tailWord_3026514, baseEnd_3026514] using wordTrace_append hprefix tailTrace_3026514
  have hstable : (prefixWord ++ tailWord_3026514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026514).length < 2 ^ (prefixWord ++ tailWord_3026514).sum := by decide
  have hdescent : baseEnd_3026514 < baseStart_3026514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026647 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3026647 : Nat := 118140960795 + 3026647 * 2 ^ 59
def prefixEnd_3026647 : Nat := 4983230072969 + 3 ^ 40 * 3026647 * 2
def baseEnd_3026647 : Nat := 1036083121659149975595473

theorem tailTrace_3026647 : CollatzResearch.WordTrace tailWord_3026647 prefixEnd_3026647 1036083121659149975595473 := by
  unfold tailWord_3026647
  simp only [CollatzResearch.WordTrace]
  refine ⟨110390885065982303999390195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73593923377321535999593463 110390885065982303999390195)
  ·
    refine ⟨165586327598973455999085293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110390885065982303999390195 165586327598973455999085293)
    ·
      refine ⟨62094872849615045999656985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165586327598973455999085293 62094872849615045999656985)
      ·
        refine ⟨46571154637211284499742739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62094872849615045999656985 46571154637211284499742739)
        ·
          refine ⟨69856731955816926749614109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46571154637211284499742739 69856731955816926749614109)
          ·
            refine ⟨26196274483431347531105291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69856731955816926749614109 26196274483431347531105291)
            ·
              refine ⟨39294411725147021296657937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26196274483431347531105291 39294411725147021296657937)
              ·
                refine ⟨29470808793860265972493453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39294411725147021296657937 29470808793860265972493453)
                ·
                  refine ⟨11051553297697599739685045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29470808793860265972493453 11051553297697599739685045)
                  ·
                    refine ⟨1036083121659149975595473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11051553297697599739685045 1036083121659149975595473)
                    ·
                      rfl

theorem cell22_3026647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3026647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026647 prefixEnd_3026647 := by exact prefixLift 3026647
  have htrace : WordTrace (prefixWord ++ tailWord_3026647) baseStart_3026647 baseEnd_3026647 := by
    simpa [prefixWord, tailWord_3026647, baseEnd_3026647] using wordTrace_append hprefix tailTrace_3026647
  have hstable : (prefixWord ++ tailWord_3026647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026647).length < 2 ^ (prefixWord ++ tailWord_3026647).sum := by decide
  have hdescent : baseEnd_3026647 < baseStart_3026647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026664 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3026664 : Nat := 118140960795 + 3026664 * 2 ^ 59
def prefixEnd_3026664 : Nat := 4983230072969 + 3 ^ 40 * 3026664 * 2
def baseEnd_3026664 : Nat := 1036088941106567597920421

theorem tailTrace_3026664 : CollatzResearch.WordTrace tailWord_3026664 prefixEnd_3026664 1036088941106567597920421 := by
  unfold tailWord_3026664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195752553460357951379523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73594336737947143935172697 55195752553460357951379523)
  ·
    refine ⟨82793628830190536927069285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55195752553460357951379523 82793628830190536927069285)
    ·
      refine ⟨15523805405660725673825491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82793628830190536927069285 15523805405660725673825491)
      ·
        refine ⟨23285708108491088510738237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15523805405660725673825491 23285708108491088510738237)
        ·
          refine ⟨8732140540684158191526839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23285708108491088510738237 8732140540684158191526839)
          ·
            refine ⟨13098210811026237287290259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8732140540684158191526839 13098210811026237287290259)
            ·
              refine ⟨19647316216539355930935389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13098210811026237287290259 19647316216539355930935389)
              ·
                refine ⟨7367743581202258474100771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19647316216539355930935389 7367743581202258474100771)
                ·
                  refine ⟨11051615371803387711151157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7367743581202258474100771 11051615371803387711151157)
                  ·
                    refine ⟨1036088941106567597920421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11051615371803387711151157 1036088941106567597920421)
                    ·
                      rfl

theorem cell22_3026664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3026664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026664 prefixEnd_3026664 := by exact prefixLift 3026664
  have htrace : WordTrace (prefixWord ++ tailWord_3026664) baseStart_3026664 baseEnd_3026664 := by
    simpa [prefixWord, tailWord_3026664, baseEnd_3026664] using wordTrace_append hprefix tailTrace_3026664
  have hstable : (prefixWord ++ tailWord_3026664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026664).length < 2 ^ (prefixWord ++ tailWord_3026664).sum := by decide
  have hdescent : baseEnd_3026664 < baseStart_3026664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026679 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3026679 : Nat := 118140960795 + 3026679 * 2 ^ 59
def prefixEnd_3026679 : Nat := 4983230072969 + 3 ^ 40 * 3026679 * 2
def baseEnd_3026679 : Nat := 1036094075913112558795375

theorem tailTrace_3026679 : CollatzResearch.WordTrace tailWord_3026679 prefixEnd_3026679 1036094075913112558795375 := by
  unfold tailWord_3026679
  simp only [CollatzResearch.WordTrace]
  refine ⟨110392052201866373464555091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73594701467910915643036727 110392052201866373464555091)
  ·
    refine ⟨165588078302799560196832637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110392052201866373464555091 165588078302799560196832637)
    ·
      refine ⟨62095529363549835073812239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165588078302799560196832637 62095529363549835073812239)
      ·
        refine ⟨93143294045324752610718359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62095529363549835073812239 93143294045324752610718359)
        ·
          refine ⟨139714941067987128916077539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93143294045324752610718359 139714941067987128916077539)
          ·
            refine ⟨209572411601980693374116309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139714941067987128916077539 209572411601980693374116309)
            ·
              refine ⟨4911853396921422500955851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209572411601980693374116309 4911853396921422500955851)
              ·
                refine ⟨7367780095382133751433777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4911853396921422500955851 7367780095382133751433777)
                ·
                  refine ⟨5525835071536600313575333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367780095382133751433777 5525835071536600313575333)
                  ·
                    refine ⟨1036094075913112558795375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525835071536600313575333 1036094075913112558795375)
                    ·
                      rfl

theorem cell22_3026679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3026679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026679 prefixEnd_3026679 := by exact prefixLift 3026679
  have htrace : WordTrace (prefixWord ++ tailWord_3026679) baseStart_3026679 baseEnd_3026679 := by
    simpa [prefixWord, tailWord_3026679, baseEnd_3026679] using wordTrace_append hprefix tailTrace_3026679
  have hstable : (prefixWord ++ tailWord_3026679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026679).length < 2 ^ (prefixWord ++ tailWord_3026679).sum := by decide
  have hdescent : baseEnd_3026679 < baseStart_3026679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026698 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_3026698 : Nat := 118140960795 + 3026698 * 2 ^ 59
def prefixEnd_3026698 : Nat := 4983230072969 + 3 ^ 40 * 3026698 * 2
def baseEnd_3026698 : Nat := 1036100580001402842570317

theorem tailTrace_3026698 : CollatzResearch.WordTrace tailWord_3026698 prefixEnd_3026698 1036100580001402842570317 := by
  unfold tailWord_3026698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27598186297199384927374187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73595163459198359806331165 27598186297199384927374187)
  ·
    refine ⟨41397279445799077391061281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27598186297199384927374187 41397279445799077391061281)
    ·
      refine ⟨31047959584349308043295961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41397279445799077391061281 31047959584349308043295961)
      ·
        refine ⟨23285969688261981032471971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31047959584349308043295961 23285969688261981032471971)
        ·
          refine ⟨34928954532392971548707957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23285969688261981032471971 34928954532392971548707957)
          ·
            refine ⟨3274589487411841082691371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34928954532392971548707957 3274589487411841082691371)
            ·
              refine ⟨4911884231117761624037057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274589487411841082691371 4911884231117761624037057)
              ·
                refine ⟨3683913173338321218027793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4911884231117761624037057 3683913173338321218027793)
                ·
                  refine ⟨2762934880003740913520845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683913173338321218027793 2762934880003740913520845)
                  ·
                    refine ⟨1036100580001402842570317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762934880003740913520845 1036100580001402842570317)
                    ·
                      rfl

theorem cell22_3026698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_3026698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026698 prefixEnd_3026698 := by exact prefixLift 3026698
  have htrace : WordTrace (prefixWord ++ tailWord_3026698) baseStart_3026698 baseEnd_3026698 := by
    simpa [prefixWord, tailWord_3026698, baseEnd_3026698] using wordTrace_append hprefix tailTrace_3026698
  have hstable : (prefixWord ++ tailWord_3026698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026698).length < 2 ^ (prefixWord ++ tailWord_3026698).sum := by decide
  have hdescent : baseEnd_3026698 < baseStart_3026698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026707 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_3026707 : Nat := 118140960795 + 3026707 * 2 ^ 59
def prefixEnd_3026707 : Nat := 4983230072969 + 3 ^ 40 * 3026707 * 2
def baseEnd_3026707 : Nat := 1036103660885329819095289

theorem tailTrace_3026707 : CollatzResearch.WordTrace tailWord_3026707 prefixEnd_3026707 1036103660885329819095289 := by
  unfold tailWord_3026707
  simp only [CollatzResearch.WordTrace]
  refine ⟨110393073445764934246574375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73595382297176622831049583 110393073445764934246574375)
  ·
    refine ⟨165589610168647401369861563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110393073445764934246574375 165589610168647401369861563)
    ·
      refine ⟨248384415252971102054792345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165589610168647401369861563 248384415252971102054792345)
      ·
        refine ⟨186288311439728326541094259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248384415252971102054792345 186288311439728326541094259)
        ·
          refine ⟨279432467159592489811641389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186288311439728326541094259 279432467159592489811641389)
          ·
            refine ⟨104787175184847183679365521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279432467159592489811641389 104787175184847183679365521)
            ·
              refine ⟨78590381388635387759524141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104787175184847183679365521 78590381388635387759524141)
              ·
                refine ⟨29471393020738270409821553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78590381388635387759524141 29471393020738270409821553)
                ·
                  refine ⟨22103544765553702807366165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29471393020738270409821553 22103544765553702807366165)
                  ·
                    refine ⟨1036103660885329819095289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22103544765553702807366165 1036103660885329819095289)
                    ·
                      rfl

theorem cell22_3026707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_3026707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026707 prefixEnd_3026707 := by exact prefixLift 3026707
  have htrace : WordTrace (prefixWord ++ tailWord_3026707) baseStart_3026707 baseEnd_3026707 := by
    simpa [prefixWord, tailWord_3026707, baseEnd_3026707] using wordTrace_append hprefix tailTrace_3026707
  have hstable : (prefixWord ++ tailWord_3026707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026707).length < 2 ^ (prefixWord ++ tailWord_3026707).sum := by decide
  have hdescent : baseEnd_3026707 < baseStart_3026707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026760 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3026760 : Nat := 118140960795 + 3026760 * 2 ^ 59
def prefixEnd_3026760 : Nat := 4983230072969 + 3 ^ 40 * 3026760 * 2
def baseEnd_3026760 : Nat := 1036121803868455347520127

theorem tailTrace_3026760 : CollatzResearch.WordTrace tailWord_3026760 prefixEnd_3026760 1036121803868455347520127 := by
  unfold tailWord_3026760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55197503257286462149126867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73596671009715282865502489 55197503257286462149126867)
  ·
    refine ⟨82796254885929693223690301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55197503257286462149126867 82796254885929693223690301)
    ·
      refine ⟨31048595582223634958883863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82796254885929693223690301 31048595582223634958883863)
      ·
        refine ⟨46572893373335452438325795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31048595582223634958883863 46572893373335452438325795)
        ·
          refine ⟨69859340060003178657488693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46572893373335452438325795 69859340060003178657488693)
          ·
            refine ⟨6549313130625297999139565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69859340060003178657488693 6549313130625297999139565)
            ·
              refine ⟨2455992423984486749677337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6549313130625297999139565 2455992423984486749677337)
              ·
                refine ⟨1841994317988365062258003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455992423984486749677337 1841994317988365062258003)
                ·
                  refine ⟨2762991476982547593387005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841994317988365062258003 2762991476982547593387005)
                  ·
                    refine ⟨1036121803868455347520127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762991476982547593387005 1036121803868455347520127)
                    ·
                      rfl

theorem cell22_3026760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3026760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026760 prefixEnd_3026760 := by exact prefixLift 3026760
  have htrace : WordTrace (prefixWord ++ tailWord_3026760) baseStart_3026760 baseEnd_3026760 := by
    simpa [prefixWord, tailWord_3026760, baseEnd_3026760] using wordTrace_append hprefix tailTrace_3026760
  have hstable : (prefixWord ++ tailWord_3026760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026760).length < 2 ^ (prefixWord ++ tailWord_3026760).sum := by decide
  have hdescent : baseEnd_3026760 < baseStart_3026760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026773 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 5]
def baseStart_3026773 : Nat := 118140960795 + 3026773 * 2 ^ 59
def prefixEnd_3026773 : Nat := 4983230072969 + 3 ^ 40 * 3026773 * 2
def baseEnd_3026773 : Nat := 345375418011375882315029

theorem tailTrace_3026773 : CollatzResearch.WordTrace tailWord_3026773 prefixEnd_3026773 345375418011375882315029 := by
  unfold tailWord_3026773
  simp only [CollatzResearch.WordTrace]
  refine ⟨110395480663525827518476973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73596987109017218345651315 110395480663525827518476973)
  ·
    refine ⟨41398305248822185319428865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110395480663525827518476973 41398305248822185319428865)
    ·
      refine ⟨31048728936616638989571649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41398305248822185319428865 31048728936616638989571649)
      ·
        refine ⟨23286546702462479242178737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31048728936616638989571649 23286546702462479242178737)
        ·
          refine ⟨17464910026846859431634053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23286546702462479242178737 17464910026846859431634053)
          ·
            refine ⟨3274670630033786143431385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17464910026846859431634053 3274670630033786143431385)
            ·
              refine ⟨2456002972525339607573539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274670630033786143431385 2456002972525339607573539)
              ·
                refine ⟨3684004458788009411360309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456002972525339607573539 3684004458788009411360309)
                ·
                  refine ⟨345375418011375882315029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684004458788009411360309 345375418011375882315029)
                  ·
                    rfl

theorem cell22_3026773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_3026773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026773 prefixEnd_3026773 := by exact prefixLift 3026773
  have htrace : WordTrace (prefixWord ++ tailWord_3026773) baseStart_3026773 baseEnd_3026773 := by
    simpa [prefixWord, tailWord_3026773, baseEnd_3026773] using wordTrace_append hprefix tailTrace_3026773
  have hstable : (prefixWord ++ tailWord_3026773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026773).length < 2 ^ (prefixWord ++ tailWord_3026773).sum := by decide
  have hdescent : baseEnd_3026773 < baseStart_3026773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026801 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 4]
def baseStart_3026801 : Nat := 118140960795 + 3026801 * 2 ^ 59
def prefixEnd_3026801 : Nat := 4983230072969 + 3 ^ 40 * 3026801 * 2
def baseEnd_3026801 : Nat := 345378613002114969081667

theorem tailTrace_3026801 : CollatzResearch.WordTrace tailWord_3026801 prefixEnd_3026801 345378613002114969081667 := by
  unfold tailWord_3026801
  simp only [CollatzResearch.WordTrace]
  refine ⟨110396501907424388300496257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73597667938282925533664171 110396501907424388300496257)
  ·
    refine ⟨82797376430568291225372193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110396501907424388300496257 82797376430568291225372193)
    ·
      refine ⟨62098032322926218419029145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82797376430568291225372193 62098032322926218419029145)
      ·
        refine ⟨46573524242194663814271859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62098032322926218419029145 46573524242194663814271859)
        ·
          refine ⟨69860286363291995721407789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46573524242194663814271859 69860286363291995721407789)
          ·
            refine ⟨26197607386234498395527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69860286363291995721407789 26197607386234498395527921)
            ·
              refine ⟨19648205539675873796645941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26197607386234498395527921 19648205539675873796645941)
              ·
                refine ⟨1842019269344613168435557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19648205539675873796645941 1842019269344613168435557)
                ·
                  refine ⟨345378613002114969081667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842019269344613168435557 345378613002114969081667)
                  ·
                    rfl

theorem cell22_3026801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_3026801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026801 prefixEnd_3026801 := by exact prefixLift 3026801
  have htrace : WordTrace (prefixWord ++ tailWord_3026801) baseStart_3026801 baseEnd_3026801 := by
    simpa [prefixWord, tailWord_3026801, baseEnd_3026801] using wordTrace_append hprefix tailTrace_3026801
  have hstable : (prefixWord ++ tailWord_3026801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026801).length < 2 ^ (prefixWord ++ tailWord_3026801).sum := by decide
  have hdescent : baseEnd_3026801 < baseStart_3026801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026878 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3026878 : Nat := 118140960795 + 3026878 * 2 ^ 59
def prefixEnd_3026878 : Nat := 4983230072969 + 3 ^ 40 * 3026878 * 2
def baseEnd_3026878 : Nat := 1036162197679942373069765

theorem tailTrace_3026878 : CollatzResearch.WordTrace tailWord_3026878 prefixEnd_3026878 1036162197679942373069765 := by
  unfold tailWord_3026878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799913791018178806381161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73599540218763620300699525 13799913791018178806381161)
  ·
    refine ⟨10349935343263634104785871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13799913791018178806381161 10349935343263634104785871)
    ·
      refine ⟨15524903014895451157178807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10349935343263634104785871 15524903014895451157178807)
      ·
        refine ⟨23287354522343176735768211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524903014895451157178807 23287354522343176735768211)
        ·
          refine ⟨34931031783514765103652317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23287354522343176735768211 34931031783514765103652317)
          ·
            refine ⟨13099136918818036913869619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34931031783514765103652317 13099136918818036913869619)
            ·
              refine ⟨19648705378227055370804429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099136918818036913869619 19648705378227055370804429)
              ·
                refine ⟨7368264516835145764051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19648705378227055370804429 7368264516835145764051661)
                ·
                  refine ⟨2763099193813179661519373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7368264516835145764051661 2763099193813179661519373)
                  ·
                    refine ⟨1036162197679942373069765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2763099193813179661519373 1036162197679942373069765)
                    ·
                      rfl

theorem cell22_3026878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3026878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026878 prefixEnd_3026878 := by exact prefixLift 3026878
  have htrace : WordTrace (prefixWord ++ tailWord_3026878) baseStart_3026878 baseEnd_3026878 := by
    simpa [prefixWord, tailWord_3026878, baseEnd_3026878] using wordTrace_append hprefix tailTrace_3026878
  have hstable : (prefixWord ++ tailWord_3026878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026878).length < 2 ^ (prefixWord ++ tailWord_3026878).sum := by decide
  have hdescent : baseEnd_3026878 < baseStart_3026878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026936 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_3026936 : Nat := 118140960795 + 3026936 * 2 ^ 59
def prefixEnd_3026936 : Nat := 4983230072969 + 3 ^ 40 * 3026936 * 2
def baseEnd_3026936 : Nat := 345394017421749851706529

theorem tailTrace_3026936 : CollatzResearch.WordTrace tailWord_3026936 prefixEnd_3026936 345394017421749851706529 := by
  unfold tailWord_3026936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55200712880967653178330331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73600950507956870904440441 55200712880967653178330331)
  ·
    refine ⟨82801069321451479767495497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55200712880967653178330331 82801069321451479767495497)
    ·
      refine ⟨62100801991088609825621623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82801069321451479767495497 62100801991088609825621623)
      ·
        refine ⟨93151202986632914738432435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62100801991088609825621623 93151202986632914738432435)
        ·
          refine ⟨139726804479949372107648653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93151202986632914738432435 139726804479949372107648653)
          ·
            refine ⟨52397551679981014540368245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139726804479949372107648653 52397551679981014540368245)
            ·
              refine ⟨4912270469998220113159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52397551679981014540368245 4912270469998220113159523)
              ·
                refine ⟨7368405704997330169739285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912270469998220113159523 7368405704997330169739285)
                ·
                  refine ⟨345394017421749851706529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7368405704997330169739285 345394017421749851706529)
                  ·
                    rfl

theorem cell22_3026936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_3026936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026936 prefixEnd_3026936 := by exact prefixLift 3026936
  have htrace : WordTrace (prefixWord ++ tailWord_3026936) baseStart_3026936 baseEnd_3026936 := by
    simpa [prefixWord, tailWord_3026936, baseEnd_3026936] using wordTrace_append hprefix tailTrace_3026936
  have hstable : (prefixWord ++ tailWord_3026936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026936).length < 2 ^ (prefixWord ++ tailWord_3026936).sum := by decide
  have hdescent : baseEnd_3026936 < baseStart_3026936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026942 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_3026942 : Nat := 118140960795 + 3026942 * 2 ^ 59
def prefixEnd_3026942 : Nat := 4983230072969 + 3 ^ 40 * 3026942 * 2
def baseEnd_3026942 : Nat := 345394702062622513156523

theorem tailTrace_3026942 : CollatzResearch.WordTrace tailWord_3026942 prefixEnd_3026942 345394702062622513156523 := by
  unfold tailWord_3026942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800205574989196172672385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73601096399942379587586053 13800205574989196172672385)
  ·
    refine ⟨10350154181241897129504289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13800205574989196172672385 10350154181241897129504289)
    ·
      refine ⟨7762615635931422847128217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350154181241897129504289 7762615635931422847128217)
      ·
        refine ⟨5821961726948567135346163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7762615635931422847128217 5821961726948567135346163)
        ·
          refine ⟨8732942590422850703019245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5821961726948567135346163 8732942590422850703019245)
          ·
            refine ⟨3274853471408569013632217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8732942590422850703019245 3274853471408569013632217)
            ·
              refine ⟨2456140103556426760224163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274853471408569013632217 2456140103556426760224163)
              ·
                refine ⟨3684210155334640140336245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456140103556426760224163 3684210155334640140336245)
                ·
                  refine ⟨345394702062622513156523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684210155334640140336245 345394702062622513156523)
                  ·
                    rfl

theorem cell22_3026942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_3026942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3026942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3026942 prefixEnd_3026942 := by exact prefixLift 3026942
  have htrace : WordTrace (prefixWord ++ tailWord_3026942) baseStart_3026942 baseEnd_3026942 := by
    simpa [prefixWord, tailWord_3026942, baseEnd_3026942] using wordTrace_append hprefix tailTrace_3026942
  have hstable : (prefixWord ++ tailWord_3026942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026942).length < 2 ^ (prefixWord ++ tailWord_3026942).sum := by decide
  have hdescent : baseEnd_3026942 < baseStart_3026942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027043 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 5]
def baseStart_3027043 : Nat := 118140960795 + 3027043 * 2 ^ 59
def prefixEnd_3027043 : Nat := 4983230072969 + 3 ^ 40 * 3027043 * 2
def baseEnd_3027043 : Nat := 345406226850645647564753

theorem tailTrace_3027043 : CollatzResearch.WordTrace tailWord_3027043 prefixEnd_3027043 345406226850645647564753 := by
  unfold tailWord_3027043
  simp only [CollatzResearch.WordTrace]
  refine ⟨110405328372547663630805783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73603552248365109087203855 110405328372547663630805783)
  ·
    refine ⟨165607992558821495446208675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110405328372547663630805783 165607992558821495446208675)
    ·
      refine ⟨248411988838232243169313013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165607992558821495446208675 248411988838232243169313013)
      ·
        refine ⟨23288623953584272797123095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248411988838232243169313013 23288623953584272797123095)
        ·
          refine ⟨34932935930376409195684643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23288623953584272797123095 34932935930376409195684643)
          ·
            refine ⟨52399403895564613793526965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34932935930376409195684643 52399403895564613793526965)
            ·
              refine ⟨4912444115209182543143153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52399403895564613793526965 4912444115209182543143153)
              ·
                refine ⟨3684333086406886907357365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912444115209182543143153 3684333086406886907357365)
                ·
                  refine ⟨345406226850645647564753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684333086406886907357365 345406226850645647564753)
                  ·
                    rfl

theorem cell22_3027043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].length) (baseStart_3027043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027043 prefixEnd_3027043 := by exact prefixLift 3027043
  have htrace : WordTrace (prefixWord ++ tailWord_3027043) baseStart_3027043 baseEnd_3027043 := by
    simpa [prefixWord, tailWord_3027043, baseEnd_3027043] using wordTrace_append hprefix tailTrace_3027043
  have hstable : (prefixWord ++ tailWord_3027043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027043).length < 2 ^ (prefixWord ++ tailWord_3027043).sum := by decide
  have hdescent : baseEnd_3027043 < baseStart_3027043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027058 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3027058 : Nat := 118140960795 + 3027058 * 2 ^ 59
def prefixEnd_3027058 : Nat := 4983230072969 + 3 ^ 40 * 3027058 * 2
def baseEnd_3027058 : Nat := 1036223815358481903569213

theorem tailTrace_3027058 : CollatzResearch.WordTrace tailWord_3027058 prefixEnd_3027058 1036223815358481903569213 := by
  unfold tailWord_3027058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27601468866873330298150457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73603916978328880795067885 27601468866873330298150457)
  ·
    refine ⟨20701101650154997723612843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27601468866873330298150457 20701101650154997723612843)
    ·
      refine ⟨31051652475232496585419265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20701101650154997723612843 31051652475232496585419265)
      ·
        refine ⟨23288739356424372439064449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31051652475232496585419265 23288739356424372439064449)
        ·
          refine ⟨17466554517318279329298337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23288739356424372439064449 17466554517318279329298337)
          ·
            refine ⟨13099915887988709496973753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17466554517318279329298337 13099915887988709496973753)
            ·
              refine ⟨9824936915991532122730315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13099915887988709496973753 9824936915991532122730315)
              ·
                refine ⟨14737405373987298184095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824936915991532122730315 14737405373987298184095473)
                ·
                  refine ⟨11053054030490473638071605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14737405373987298184095473 11053054030490473638071605)
                  ·
                    refine ⟨1036223815358481903569213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11053054030490473638071605 1036223815358481903569213)
                    ·
                      rfl

theorem cell22_3027058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3027058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027058 prefixEnd_3027058 := by exact prefixLift 3027058
  have htrace : WordTrace (prefixWord ++ tailWord_3027058) baseStart_3027058 baseEnd_3027058 := by
    simpa [prefixWord, tailWord_3027058, baseEnd_3027058] using wordTrace_append hprefix tailTrace_3027058
  have hstable : (prefixWord ++ tailWord_3027058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027058).length < 2 ^ (prefixWord ++ tailWord_3027058).sum := by decide
  have hdescent : baseEnd_3027058 < baseStart_3027058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027090 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3027090 : Nat := 118140960795 + 3027090 * 2 ^ 59
def prefixEnd_3027090 : Nat := 4983230072969 + 3 ^ 40 * 3027090 * 2
def baseEnd_3027090 : Nat := 1036234769612444486769115

theorem tailTrace_3027090 : CollatzResearch.WordTrace tailWord_3027090 prefixEnd_3027090 1036234769612444486769115 := by
  unfold tailWord_3027090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27601760650844347664441681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73604695068918260438511149 27601760650844347664441681)
  ·
    refine ⟨20701320488133260748331261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27601760650844347664441681 20701320488133260748331261)
    ·
      refine ⟨7762995183049972780624223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20701320488133260748331261 7762995183049972780624223)
      ·
        refine ⟨11644492774574959170936335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762995183049972780624223 11644492774574959170936335)
        ·
          refine ⟨17466739161862438756404503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644492774574959170936335 17466739161862438756404503)
          ·
            refine ⟨26200108742793658134606755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17466739161862438756404503 26200108742793658134606755)
            ·
              refine ⟨39300163114190487201910133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26200108742793658134606755 39300163114190487201910133)
              ·
                refine ⟨3684390291955358175179075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39300163114190487201910133 3684390291955358175179075)
                ·
                  refine ⟨5526585437933037262768613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684390291955358175179075 5526585437933037262768613)
                  ·
                    refine ⟨1036234769612444486769115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526585437933037262768613 1036234769612444486769115)
                    ·
                      rfl

theorem cell22_3027090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3027090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027090 prefixEnd_3027090 := by exact prefixLift 3027090
  have htrace : WordTrace (prefixWord ++ tailWord_3027090) baseStart_3027090 baseEnd_3027090 := by
    simpa [prefixWord, tailWord_3027090, baseEnd_3027090] using wordTrace_append hprefix tailTrace_3027090
  have hstable : (prefixWord ++ tailWord_3027090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027090).length < 2 ^ (prefixWord ++ tailWord_3027090).sum := by decide
  have hdescent : baseEnd_3027090 < baseStart_3027090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027105 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 6]
def baseStart_3027105 : Nat := 118140960795 + 3027105 * 2 ^ 59
def prefixEnd_3027105 : Nat := 4983230072969 + 3 ^ 40 * 3027105 * 2
def baseEnd_3027105 : Nat := 345413301472996482548023

theorem tailTrace_3027105 : CollatzResearch.WordTrace tailWord_3027105 prefixEnd_3027105 345413301472996482548023 := by
  unfold tailWord_3027105
  simp only [CollatzResearch.WordTrace]
  refine ⟨110407589698323048219562769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73605059798882032146375179 110407589698323048219562769)
  ·
    refine ⟨82805692273742286164672077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110407589698323048219562769 82805692273742286164672077)
    ·
      refine ⟨31052134602653357311752029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82805692273742286164672077 31052134602653357311752029)
      ·
        refine ⟨11644550475995008991907011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31052134602653357311752029 11644550475995008991907011)
        ·
          refine ⟨17466825713992513487860517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644550475995008991907011 17466825713992513487860517)
          ·
            refine ⟨3275029821373596278973847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17466825713992513487860517 3275029821373596278973847)
            ·
              refine ⟨4912544732060394418460771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275029821373596278973847 4912544732060394418460771)
              ·
                refine ⟨7368817098090591627691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912544732060394418460771 7368817098090591627691157)
                ·
                  refine ⟨345413301472996482548023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7368817098090591627691157 345413301472996482548023)
                  ·
                    rfl

theorem cell22_3027105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_3027105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027105 prefixEnd_3027105 := by exact prefixLift 3027105
  have htrace : WordTrace (prefixWord ++ tailWord_3027105) baseStart_3027105 baseEnd_3027105 := by
    simpa [prefixWord, tailWord_3027105, baseEnd_3027105] using wordTrace_append hprefix tailTrace_3027105
  have hstable : (prefixWord ++ tailWord_3027105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027105).length < 2 ^ (prefixWord ++ tailWord_3027105).sum := by decide
  have hdescent : baseEnd_3027105 < baseStart_3027105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027137 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3027137 : Nat := 118140960795 + 3027137 * 2 ^ 59
def prefixEnd_3027137 : Nat := 4983230072969 + 3 ^ 40 * 3027137 * 2
def baseEnd_3027137 : Nat := 1036250858672952030843971

theorem tailTrace_3027137 : CollatzResearch.WordTrace tailWord_3027137 prefixEnd_3027137 1036250858672952030843971 := by
  unfold tailWord_3027137
  simp only [CollatzResearch.WordTrace]
  refine ⟨110408756834207117684727665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73605837889471411789818443 110408756834207117684727665)
  ·
    refine ⟨82806567625655338263545749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110408756834207117684727665 82806567625655338263545749)
    ·
      refine ⟨3881557857452593981103707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82806567625655338263545749 3881557857452593981103707)
      ·
        refine ⟨5822336786178890971655561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881557857452593981103707 5822336786178890971655561)
        ·
          refine ⟨4366752589634168228741671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822336786178890971655561 4366752589634168228741671)
          ·
            refine ⟨6550128884451252343112507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366752589634168228741671 6550128884451252343112507)
            ·
              refine ⟨9825193326676878514668761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550128884451252343112507 9825193326676878514668761)
              ·
                refine ⟨7368894995007658886001571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9825193326676878514668761 7368894995007658886001571)
                ·
                  refine ⟨11053342492511488329002357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368894995007658886001571 11053342492511488329002357)
                  ·
                    refine ⟨1036250858672952030843971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11053342492511488329002357 1036250858672952030843971)
                    ·
                      rfl

theorem cell22_3027137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3027137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027137 prefixEnd_3027137 := by exact prefixLift 3027137
  have htrace : WordTrace (prefixWord ++ tailWord_3027137) baseStart_3027137 baseEnd_3027137 := by
    simpa [prefixWord, tailWord_3027137, baseEnd_3027137] using wordTrace_append hprefix tailTrace_3027137
  have hstable : (prefixWord ++ tailWord_3027137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027137).length < 2 ^ (prefixWord ++ tailWord_3027137).sum := by decide
  have hdescent : baseEnd_3027137 < baseStart_3027137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027229 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 5]
def baseStart_3027229 : Nat := 118140960795 + 3027229 * 2 ^ 59
def prefixEnd_3027229 : Nat := 4983230072969 + 3 ^ 40 * 3027229 * 2
def baseEnd_3027229 : Nat := 345427450717698152514563

theorem tailTrace_3027229 : CollatzResearch.WordTrace tailWord_3027229 prefixEnd_3027229 345427450717698152514563 := by
  unfold tailWord_3027229
  simp only [CollatzResearch.WordTrace]
  refine ⟨110412112349873817397076741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73608074899915878264717827 110412112349873817397076741)
  ·
    refine ⟨20702271065601340761951889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110412112349873817397076741 20702271065601340761951889)
    ·
      refine ⟨15526703299201005571463917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20702271065601340761951889 15526703299201005571463917)
      ·
        refine ⟨5822513737200377089298969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15526703299201005571463917 5822513737200377089298969)
        ·
          refine ⟨4366885302900282816974227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822513737200377089298969 4366885302900282816974227)
          ·
            refine ⟨6550327954350424225461341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366885302900282816974227 6550327954350424225461341)
            ·
              refine ⟨2456372982881409084548003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6550327954350424225461341 2456372982881409084548003)
              ·
                refine ⟨3684559474322113626822005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456372982881409084548003 3684559474322113626822005)
                ·
                  refine ⟨345427450717698152514563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684559474322113626822005 345427450717698152514563)
                  ·
                    rfl

theorem cell22_3027229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_3027229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027229 prefixEnd_3027229 := by exact prefixLift 3027229
  have htrace : WordTrace (prefixWord ++ tailWord_3027229) baseStart_3027229 baseEnd_3027229 := by
    simpa [prefixWord, tailWord_3027229, baseEnd_3027229] using wordTrace_append hprefix tailTrace_3027229
  have hstable : (prefixWord ++ tailWord_3027229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027229).length < 2 ^ (prefixWord ++ tailWord_3027229).sum := by decide
  have hdescent : baseEnd_3027229 < baseStart_3027229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027283 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_3027283 : Nat := 118140960795 + 3027283 * 2 ^ 59
def prefixEnd_3027283 : Nat := 4983230072969 + 3 ^ 40 * 3027283 * 2
def baseEnd_3027283 : Nat := 1036300837456656316693523

theorem tailTrace_3027283 : CollatzResearch.WordTrace tailWord_3027283 prefixEnd_3027283 1036300837456656316693523 := by
  unfold tailWord_3027283
  simp only [CollatzResearch.WordTrace]
  refine ⟨110414081891678184619542503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73609387927785456413028335 110414081891678184619542503)
  ·
    refine ⟨165621122837517276929313755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110414081891678184619542503 165621122837517276929313755)
    ·
      refine ⟨248431684256275915393970633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165621122837517276929313755 248431684256275915393970633)
      ·
        refine ⟨186323763192206936545477975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248431684256275915393970633 186323763192206936545477975)
        ·
          refine ⟨279485644788310404818216963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186323763192206936545477975 279485644788310404818216963)
          ·
            refine ⟨419228467182465607227325445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279485644788310404818216963 419228467182465607227325445)
            ·
              refine ⟨78605337596712301355123521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419228467182465607227325445 78605337596712301355123521)
              ·
                refine ⟨58954003197534226016342641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78605337596712301355123521 58954003197534226016342641)
                ·
                  refine ⟨44215502398150669512256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58954003197534226016342641 44215502398150669512256981)
                  ·
                    refine ⟨1036300837456656316693523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44215502398150669512256981 1036300837456656316693523)
                    ·
                      rfl

theorem cell22_3027283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_3027283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027283 prefixEnd_3027283 := by exact prefixLift 3027283
  have htrace : WordTrace (prefixWord ++ tailWord_3027283) baseStart_3027283 baseEnd_3027283 := by
    simpa [prefixWord, tailWord_3027283, baseEnd_3027283] using wordTrace_append hprefix tailTrace_3027283
  have hstable : (prefixWord ++ tailWord_3027283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027283).length < 2 ^ (prefixWord ++ tailWord_3027283).sum := by decide
  have hdescent : baseEnd_3027283 < baseStart_3027283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027368 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3027368 : Nat := 118140960795 + 3027368 * 2 ^ 59
def prefixEnd_3027368 : Nat := 4983230072969 + 3 ^ 40 * 3027368 * 2
def baseEnd_3027368 : Nat := 1036329934693744428318263

theorem tailTrace_3027368 : CollatzResearch.WordTrace tailWord_3027368 prefixEnd_3027368 1036329934693744428318263 := by
  unfold tailWord_3027368
  simp only [CollatzResearch.WordTrace]
  refine ⟨55208591048185122068193379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73611454730913496090924505 55208591048185122068193379)
  ·
    refine ⟨82812886572277683102290069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55208591048185122068193379 82812886572277683102290069)
    ·
      refine ⟨3881854058075516395419847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82812886572277683102290069 3881854058075516395419847)
      ·
        refine ⟨5822781087113274593129771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881854058075516395419847 5822781087113274593129771)
        ·
          refine ⟨8734171630669911889694657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822781087113274593129771 8734171630669911889694657)
          ·
            refine ⟨6550628723002433917270993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8734171630669911889694657 6550628723002433917270993)
            ·
              refine ⟨4912971542251825437953245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6550628723002433917270993 4912971542251825437953245)
              ·
                refine ⟨1842364328344434539232467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4912971542251825437953245 1842364328344434539232467)
                ·
                  refine ⟨2763546492516651808848701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842364328344434539232467 2763546492516651808848701)
                  ·
                    refine ⟨1036329934693744428318263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2763546492516651808848701 1036329934693744428318263)
                    ·
                      rfl

theorem cell22_3027368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3027368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027368 prefixEnd_3027368 := by exact prefixLift 3027368
  have htrace : WordTrace (prefixWord ++ tailWord_3027368) baseStart_3027368 baseEnd_3027368 := by
    simpa [prefixWord, tailWord_3027368, baseEnd_3027368] using wordTrace_append hprefix tailTrace_3027368
  have hstable : (prefixWord ++ tailWord_3027368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027368).length < 2 ^ (prefixWord ++ tailWord_3027368).sum := by decide
  have hdescent : baseEnd_3027368 < baseStart_3027368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027381 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 5]
def baseStart_3027381 : Nat := 118140960795 + 3027381 * 2 ^ 59
def prefixEnd_3027381 : Nat := 4983230072969 + 3 ^ 40 * 3027381 * 2
def baseEnd_3027381 : Nat := 345444794953138909247741

theorem tailTrace_3027381 : CollatzResearch.WordTrace tailWord_3027381 prefixEnd_3027381 345444794953138909247741 := by
  unfold tailWord_3027381
  simp only [CollatzResearch.WordTrace]
  refine ⟨110417656245323147356609997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73611770830215431571073331 110417656245323147356609997)
  ·
    refine ⟨41406621091996180258728749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110417656245323147356609997 41406621091996180258728749)
    ·
      refine ⟨15527482909498567597023281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41406621091996180258728749 15527482909498567597023281)
      ·
        refine ⟨11645612182123925697767461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15527482909498567597023281 11645612182123925697767461)
        ·
          refine ⟨2183552284148236068331399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11645612182123925697767461 2183552284148236068331399)
          ·
            refine ⟨3275328426222354102497099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183552284148236068331399 3275328426222354102497099)
            ·
              refine ⟨4912992639333531153745649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275328426222354102497099 4912992639333531153745649)
              ·
                refine ⟨3684744479500148365309237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912992639333531153745649 3684744479500148365309237)
                ·
                  refine ⟨345444794953138909247741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684744479500148365309237 345444794953138909247741)
                  ·
                    rfl

theorem cell22_3027381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_3027381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027381 prefixEnd_3027381 := by exact prefixLift 3027381
  have htrace : WordTrace (prefixWord ++ tailWord_3027381) baseStart_3027381 baseEnd_3027381 := by
    simpa [prefixWord, tailWord_3027381, baseEnd_3027381] using wordTrace_append hprefix tailTrace_3027381
  have hstable : (prefixWord ++ tailWord_3027381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027381).length < 2 ^ (prefixWord ++ tailWord_3027381).sum := by decide
  have hdescent : baseEnd_3027381 < baseStart_3027381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027437 : List Nat := [1, 5, 1, 3, 1, 1, 10]
def baseStart_3027437 : Nat := 118140960795 + 3027437 * 2 ^ 59
def prefixEnd_3027437 : Nat := 4983230072969 + 3 ^ 40 * 3027437 * 2
def baseEnd_3027437 : Nat := 38383464992735231420113

theorem tailTrace_3027437 : CollatzResearch.WordTrace tailWord_3027437 prefixEnd_3027437 38383464992735231420113 := by
  unfold tailWord_3027437
  simp only [CollatzResearch.WordTrace]
  refine ⟨110419698733120268920648565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73613132488746845947099043 110419698733120268920648565)
  ·
    refine ⟨10351846756230025211310803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110419698733120268920648565 10351846756230025211310803)
    ·
      refine ⟨15527770134345037816966205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10351846756230025211310803 15527770134345037816966205)
      ·
        refine ⟨5822913800379389181362327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15527770134345037816966205 5822913800379389181362327)
        ·
          refine ⟨8734370700569083772043491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822913800379389181362327 8734370700569083772043491)
          ·
            refine ⟨13101556050853625658065237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8734370700569083772043491 13101556050853625658065237)
            ·
              refine ⟨38383464992735231420113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13101556050853625658065237 38383464992735231420113)
              ·
                rfl

theorem cell22_3027437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 10].length) (baseStart_3027437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027437 prefixEnd_3027437 := by exact prefixLift 3027437
  have htrace : WordTrace (prefixWord ++ tailWord_3027437) baseStart_3027437 baseEnd_3027437 := by
    simpa [prefixWord, tailWord_3027437, baseEnd_3027437] using wordTrace_append hprefix tailTrace_3027437
  have hstable : (prefixWord ++ tailWord_3027437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027437).length < 2 ^ (prefixWord ++ tailWord_3027437).sum := by decide
  have hdescent : baseEnd_3027437 < baseStart_3027437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027458 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3027458 : Nat := 118140960795 + 3027458 * 2 ^ 59
def prefixEnd_3027458 : Nat := 4983230072969 + 3 ^ 40 * 3027458 * 2
def baseEnd_3027458 : Nat := 1036360743533014193567987

theorem tailTrace_3027458 : CollatzResearch.WordTrace tailWord_3027458 prefixEnd_3027458 1036360743533014193567987 := by
  unfold tailWord_3027458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605116166511047376790757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73613643110696126338108685 27605116166511047376790757)
  ·
    refine ⟨5175959281220821383148267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27605116166511047376790757 5175959281220821383148267)
    ·
      refine ⟨7763938921831232074722401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175959281220821383148267 7763938921831232074722401)
      ·
        refine ⟨5822954191373424056041801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7763938921831232074722401 5822954191373424056041801)
        ·
          refine ⟨4367215643530068042031351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822954191373424056041801 4367215643530068042031351)
          ·
            refine ⟨6550823465295102063047027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367215643530068042031351 6550823465295102063047027)
            ·
              refine ⟨9826235197942653094570541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550823465295102063047027 9826235197942653094570541)
              ·
                refine ⟨3684838199228494910463953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9826235197942653094570541 3684838199228494910463953)
                ·
                  refine ⟨2763628649421371182847965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3684838199228494910463953 2763628649421371182847965)
                  ·
                    refine ⟨1036360743533014193567987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2763628649421371182847965 1036360743533014193567987)
                    ·
                      rfl

theorem cell22_3027458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3027458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027458 prefixEnd_3027458 := by exact prefixLift 3027458
  have htrace : WordTrace (prefixWord ++ tailWord_3027458) baseStart_3027458 baseEnd_3027458 := by
    simpa [prefixWord, tailWord_3027458, baseEnd_3027458] using wordTrace_append hprefix tailTrace_3027458
  have hstable : (prefixWord ++ tailWord_3027458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027458).length < 2 ^ (prefixWord ++ tailWord_3027458).sum := by decide
  have hdescent : baseEnd_3027458 < baseStart_3027458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027465 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 9]
def baseStart_3027465 : Nat := 118140960795 + 3027465 * 2 ^ 59
def prefixEnd_3027465 : Nat := 4983230072969 + 3 ^ 40 * 3027465 * 2
def baseEnd_3027465 : Nat := 345454379925356169547655

theorem tailTrace_3027465 : CollatzResearch.WordTrace tailWord_3027465 prefixEnd_3027465 345454379925356169547655 := by
  unfold tailWord_3027465
  simp only [CollatzResearch.WordTrace]
  refine ⟨110420719977018829702667849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73613813318012553135111899 110420719977018829702667849)
  ·
    refine ⟨82815539982764122277000887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110420719977018829702667849 82815539982764122277000887)
    ·
      refine ⟨124223309974146183415501331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82815539982764122277000887 124223309974146183415501331)
      ·
        refine ⟨186334964961219275123251997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124223309974146183415501331 186334964961219275123251997)
        ·
          refine ⟨69875611860457228171219499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186334964961219275123251997 69875611860457228171219499)
          ·
            refine ⟨104813417790685842256829249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69875611860457228171219499 104813417790685842256829249)
            ·
              refine ⟨78610063343014381692621937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104813417790685842256829249 78610063343014381692621937)
              ·
                refine ⟨58957547507260786269466453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78610063343014381692621937 58957547507260786269466453)
                ·
                  refine ⟨345454379925356169547655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58957547507260786269466453 345454379925356169547655)
                  ·
                    rfl

theorem cell22_3027465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_3027465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027465 prefixEnd_3027465 := by exact prefixLift 3027465
  have htrace : WordTrace (prefixWord ++ tailWord_3027465) baseStart_3027465 baseEnd_3027465 := by
    simpa [prefixWord, tailWord_3027465, baseEnd_3027465] using wordTrace_append hprefix tailTrace_3027465
  have hstable : (prefixWord ++ tailWord_3027465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027465).length < 2 ^ (prefixWord ++ tailWord_3027465).sum := by decide
  have hdescent : baseEnd_3027465 < baseStart_3027465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027512 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3027512 : Nat := 118140960795 + 3027512 * 2 ^ 59
def prefixEnd_3027512 : Nat := 4983230072969 + 3 ^ 40 * 3027512 * 2
def baseEnd_3027512 : Nat := 1036379228836576052717821

theorem tailTrace_3027512 : CollatzResearch.WordTrace tailWord_3027512 prefixEnd_3027512 1036379228836576052717821 := by
  unfold tailWord_3027512
  simp only [CollatzResearch.WordTrace]
  refine ⟨55211217103924278364814395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73614956138565704486419193 55211217103924278364814395)
  ·
    refine ⟨82816825655886417547221593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55211217103924278364814395 82816825655886417547221593)
    ·
      refine ⟨62112619241914813160416195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82816825655886417547221593 62112619241914813160416195)
      ·
        refine ⟨93168928862872219740624293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62112619241914813160416195 93168928862872219740624293)
        ·
          refine ⟨17469174161788541201367055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93168928862872219740624293 17469174161788541201367055)
          ·
            refine ⟨26203761242682811802050583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469174161788541201367055 26203761242682811802050583)
            ·
              refine ⟨39305641864024217703075875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26203761242682811802050583 39305641864024217703075875)
              ·
                refine ⟨58958462796036326554613813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39305641864024217703075875 58958462796036326554613813)
                ·
                  refine ⟨5527355887128405614495045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58958462796036326554613813 5527355887128405614495045)
                  ·
                    refine ⟨1036379228836576052717821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5527355887128405614495045 1036379228836576052717821)
                    ·
                      rfl

theorem cell22_3027512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3027512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027512 prefixEnd_3027512 := by exact prefixLift 3027512
  have htrace : WordTrace (prefixWord ++ tailWord_3027512) baseStart_3027512 baseEnd_3027512 := by
    simpa [prefixWord, tailWord_3027512, baseEnd_3027512] using wordTrace_append hprefix tailTrace_3027512
  have hstable : (prefixWord ++ tailWord_3027512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027512).length < 2 ^ (prefixWord ++ tailWord_3027512).sum := by decide
  have hdescent : baseEnd_3027512 < baseStart_3027512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027527 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 8]
def baseStart_3027527 : Nat := 118140960795 + 3027527 * 2 ^ 59
def prefixEnd_3027527 : Nat := 4983230072969 + 3 ^ 40 * 3027527 * 2
def baseEnd_3027527 : Nat := 345461454547707004530925

theorem tailTrace_3027527 : CollatzResearch.WordTrace tailWord_3027527 prefixEnd_3027527 345461454547707004530925 := by
  unfold tailWord_3027527
  simp only [CollatzResearch.WordTrace]
  refine ⟨110422981302794214291424835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73615320868529476194283223 110422981302794214291424835)
  ·
    refine ⟨165634471954191321437137253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110422981302794214291424835 165634471954191321437137253)
    ·
      refine ⟨31056463491410872769463235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165634471954191321437137253 31056463491410872769463235)
      ·
        refine ⟨46584695237116309154194853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31056463491410872769463235 46584695237116309154194853)
        ·
          refine ⟨8734630356959307966411535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46584695237116309154194853 8734630356959307966411535)
          ·
            refine ⟨13101945535438961949617303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8734630356959307966411535 13101945535438961949617303)
            ·
              refine ⟨19652918303158442924425955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101945535438961949617303 19652918303158442924425955)
              ·
                refine ⟨29479377454737664386638933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19652918303158442924425955 29479377454737664386638933)
                ·
                  refine ⟨345461454547707004530925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29479377454737664386638933 345461454547707004530925)
                  ·
                    rfl

theorem cell22_3027527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_3027527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027527 prefixEnd_3027527 := by exact prefixLift 3027527
  have htrace : WordTrace (prefixWord ++ tailWord_3027527) baseStart_3027527 baseEnd_3027527 := by
    simpa [prefixWord, tailWord_3027527, baseEnd_3027527] using wordTrace_append hprefix tailTrace_3027527
  have hstable : (prefixWord ++ tailWord_3027527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027527).length < 2 ^ (prefixWord ++ tailWord_3027527).sum := by decide
  have hdescent : baseEnd_3027527 < baseStart_3027527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027544 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_3027544 : Nat := 118140960795 + 3027544 * 2 ^ 59
def prefixEnd_3027544 : Nat := 4983230072969 + 3 ^ 40 * 3027544 * 2
def baseEnd_3027544 : Nat := 345463394363512878639241

theorem tailTrace_3027544 : CollatzResearch.WordTrace tailWord_3027544 prefixEnd_3027544 345463394363512878639241 := by
  unfold tailWord_3027544
  simp only [CollatzResearch.WordTrace]
  refine ⟨55211800671866313097396843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73615734229155084129862457 55211800671866313097396843)
  ·
    refine ⟨82817701007799469646095265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55211800671866313097396843 82817701007799469646095265)
    ·
      refine ⟨62113275755849602234571449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82817701007799469646095265 62113275755849602234571449)
      ·
        refine ⟨46584956816887201675928587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62113275755849602234571449 46584956816887201675928587)
        ·
          refine ⟨69877435225330802513892881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46584956816887201675928587 69877435225330802513892881)
          ·
            refine ⟨52408076418998101885419661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69877435225330802513892881 52408076418998101885419661)
            ·
              refine ⟨19653028657124288207032373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52408076418998101885419661 19653028657124288207032373)
              ·
                refine ⟨1842471436605402019409285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19653028657124288207032373 1842471436605402019409285)
                ·
                  refine ⟨345463394363512878639241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842471436605402019409285 345463394363512878639241)
                  ·
                    rfl

theorem cell22_3027544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_3027544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027544 prefixEnd_3027544 := by exact prefixLift 3027544
  have htrace : WordTrace (prefixWord ++ tailWord_3027544) baseStart_3027544 baseEnd_3027544 := by
    simpa [prefixWord, tailWord_3027544, baseEnd_3027544] using wordTrace_append hprefix tailTrace_3027544
  have hstable : (prefixWord ++ tailWord_3027544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027544).length < 2 ^ (prefixWord ++ tailWord_3027544).sum := by decide
  have hdescent : baseEnd_3027544 < baseStart_3027544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027589 : List Nat := [1, 3, 1, 1, 4, 2, 4, 6]
def baseStart_3027589 : Nat := 118140960795 + 3027589 * 2 ^ 59
def prefixEnd_3027589 : Nat := 4983230072969 + 3 ^ 40 * 3027589 * 2
def baseEnd_3027589 : Nat := 115156176390019279838065

theorem tailTrace_3027589 : CollatzResearch.WordTrace tailWord_3027589 prefixEnd_3027589 115156176390019279838065 := by
  unfold tailWord_3027589
  simp only [CollatzResearch.WordTrace]
  refine ⟨110425242628569598880181821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73616828419046399253454547 110425242628569598880181821)
  ·
    refine ⟨41409465985713599580068183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110425242628569598880181821 41409465985713599580068183)
    ·
      refine ⟨62114198978570399370102275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41409465985713599580068183 62114198978570399370102275)
      ·
        refine ⟨93171298467855599055153413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62114198978570399370102275 93171298467855599055153413)
        ·
          refine ⟨17469618462722924822841265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93171298467855599055153413 17469618462722924822841265)
          ·
            refine ⟨13102213847042193617130949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17469618462722924822841265 13102213847042193617130949)
            ·
              refine ⟨2456665096320411303212053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13102213847042193617130949 2456665096320411303212053)
              ·
                refine ⟨115156176390019279838065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2456665096320411303212053 115156176390019279838065)
                ·
                  rfl

theorem cell22_3027589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 6].length) (baseStart_3027589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027589 prefixEnd_3027589 := by exact prefixLift 3027589
  have htrace : WordTrace (prefixWord ++ tailWord_3027589) baseStart_3027589 baseEnd_3027589 := by
    simpa [prefixWord, tailWord_3027589, baseEnd_3027589] using wordTrace_append hprefix tailTrace_3027589
  have hstable : (prefixWord ++ tailWord_3027589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027589).length < 2 ^ (prefixWord ++ tailWord_3027589).sum := by decide
  have hdescent : baseEnd_3027589 < baseStart_3027589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027632 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_3027632 : Nat := 118140960795 + 3027632 * 2 ^ 59
def prefixEnd_3027632 : Nat := 4983230072969 + 3 ^ 40 * 3027632 * 2
def baseEnd_3027632 : Nat := 1036420307288935739717453

theorem tailTrace_3027632 : CollatzResearch.WordTrace tailWord_3027632 prefixEnd_3027632 1036420307288935739717453 := by
  unfold tailWord_3027632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55213405483706908611998575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73617873978275878149331433 55213405483706908611998575)
  ·
    refine ⟨82820108225560362917997863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55213405483706908611998575 82820108225560362917997863)
    ·
      refine ⟨124230162338340544376996795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82820108225560362917997863 124230162338340544376996795)
      ·
        refine ⟨186345243507510816565495193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124230162338340544376996795 186345243507510816565495193)
        ·
          refine ⟨139758932630633112424121395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186345243507510816565495193 139758932630633112424121395)
          ·
            refine ⟨209638398945949668636182093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139758932630633112424121395 209638398945949668636182093)
            ·
              refine ⟨78614399604731125738568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209638398945949668636182093 78614399604731125738568285)
              ·
                refine ⟨29480399851774172151963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78614399604731125738568285 29480399851774172151963107)
                ·
                  refine ⟨44220599777661258227944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29480399851774172151963107 44220599777661258227944661)
                  ·
                    refine ⟨1036420307288935739717453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44220599777661258227944661 1036420307288935739717453)
                    ·
                      rfl

theorem cell22_3027632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_3027632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027632 prefixEnd_3027632 := by exact prefixLift 3027632
  have htrace : WordTrace (prefixWord ++ tailWord_3027632) baseStart_3027632 baseEnd_3027632 := by
    simpa [prefixWord, tailWord_3027632, baseEnd_3027632] using wordTrace_append hprefix tailTrace_3027632
  have hstable : (prefixWord ++ tailWord_3027632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027632).length < 2 ^ (prefixWord ++ tailWord_3027632).sum := by decide
  have hdescent : baseEnd_3027632 < baseStart_3027632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027668 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3027668 : Nat := 118140960795 + 3027668 * 2 ^ 59
def prefixEnd_3027668 : Nat := 4983230072969 + 3 ^ 40 * 3027668 * 2
def baseEnd_3027668 : Nat := 345477543608214548605781

theorem tailTrace_3027668 : CollatzResearch.WordTrace tailWord_3027668 prefixEnd_3027668 345477543608214548605781 := by
  unfold tailWord_3027668
  simp only [CollatzResearch.WordTrace]
  refine ⟨55214061997641697686153829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73618749330188930248205105 55214061997641697686153829)
  ·
    refine ⟨10352636624557818316153843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55214061997641697686153829 10352636624557818316153843)
    ·
      refine ⟨15528954936836727474230765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352636624557818316153843 15528954936836727474230765)
      ·
        refine ⟨5823358101313772802836537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15528954936836727474230765 5823358101313772802836537)
        ·
          refine ⟨4367518575985329602127403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5823358101313772802836537 4367518575985329602127403)
          ·
            refine ⟨6551277863977994403191105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367518575985329602127403 6551277863977994403191105)
            ·
              refine ⟨4913458397983495802393329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6551277863977994403191105 4913458397983495802393329)
              ·
                refine ⟨3685093798487621851794997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4913458397983495802393329 3685093798487621851794997)
                ·
                  refine ⟨345477543608214548605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685093798487621851794997 345477543608214548605781)
                  ·
                    rfl

theorem cell22_3027668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3027668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027668 prefixEnd_3027668 := by exact prefixLift 3027668
  have htrace : WordTrace (prefixWord ++ tailWord_3027668) baseStart_3027668 baseEnd_3027668 := by
    simpa [prefixWord, tailWord_3027668, baseEnd_3027668] using wordTrace_append hprefix tailTrace_3027668
  have hstable : (prefixWord ++ tailWord_3027668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027668).length < 2 ^ (prefixWord ++ tailWord_3027668).sum := by decide
  have hdescent : baseEnd_3027668 < baseStart_3027668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027709 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3027709 : Nat := 118140960795 + 3027709 * 2 ^ 59
def prefixEnd_3027709 : Nat := 4983230072969 + 3 ^ 40 * 3027709 * 2
def baseEnd_3027709 : Nat := 1036446665962533205542217

theorem tailTrace_3027709 : CollatzResearch.WordTrace tailWord_3027709 prefixEnd_3027709 1036446665962533205542217 := by
  unfold tailWord_3027709
  simp only [CollatzResearch.WordTrace]
  refine ⟨110429619388134859374550181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73619746258756572916366787 110429619388134859374550181)
  ·
    refine ⟨20705553635275286132728159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110429619388134859374550181 20705553635275286132728159)
    ·
      refine ⟨31058330452912929199092239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20705553635275286132728159 31058330452912929199092239)
      ·
        refine ⟨46587495679369393798638359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31058330452912929199092239 46587495679369393798638359)
        ·
          refine ⟨69881243519054090697957539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46587495679369393798638359 69881243519054090697957539)
          ·
            refine ⟨104821865278581136046936309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69881243519054090697957539 104821865278581136046936309)
            ·
              refine ⟨9827049869866981504400279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104821865278581136046936309 9827049869866981504400279)
              ·
                refine ⟨14740574804800472256600419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9827049869866981504400279 14740574804800472256600419)
                ·
                  refine ⟨22110862207200708384900629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740574804800472256600419 22110862207200708384900629)
                  ·
                    refine ⟨1036446665962533205542217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22110862207200708384900629 1036446665962533205542217)
                    ·
                      rfl

theorem cell22_3027709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3027709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027709 prefixEnd_3027709 := by exact prefixLift 3027709
  have htrace : WordTrace (prefixWord ++ tailWord_3027709) baseStart_3027709 baseEnd_3027709 := by
    simpa [prefixWord, tailWord_3027709, baseEnd_3027709] using wordTrace_append hprefix tailTrace_3027709
  have hstable : (prefixWord ++ tailWord_3027709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027709).length < 2 ^ (prefixWord ++ tailWord_3027709).sum := by decide
  have hdescent : baseEnd_3027709 < baseStart_3027709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027756 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_3027756 : Nat := 118140960795 + 3027756 * 2 ^ 59
def prefixEnd_3027756 : Nat := 4983230072969 + 3 ^ 40 * 3027756 * 2
def baseEnd_3027756 : Nat := 1036462755023040749617073

theorem tailTrace_3027756 : CollatzResearch.WordTrace tailWord_3027756 prefixEnd_3027756 1036462755023040749617073 := by
  unfold tailWord_3027756
  simp only [CollatzResearch.WordTrace]
  refine ⟨55215666809482293200755561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73620889079309724267674081 55215666809482293200755561)
  ·
    refine ⟨41411750107111719900566671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55215666809482293200755561 41411750107111719900566671)
    ·
      refine ⟨62117625160667579850850007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41411750107111719900566671 62117625160667579850850007)
      ·
        refine ⟨93176437741001369776275011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62117625160667579850850007 93176437741001369776275011)
        ·
          refine ⟨139764656611502054664412517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93176437741001369776275011 139764656611502054664412517)
          ·
            refine ⟨26205873114656635249577347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139764656611502054664412517 26205873114656635249577347)
            ·
              refine ⟨39308809671984952874366021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26205873114656635249577347 39308809671984952874366021)
              ·
                refine ⟨7370401813497178663943629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39308809671984952874366021 7370401813497178663943629)
                ·
                  refine ⟨2763900680061441998978861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7370401813497178663943629 2763900680061441998978861)
                  ·
                    refine ⟨1036462755023040749617073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2763900680061441998978861 1036462755023040749617073)
                    ·
                      rfl

theorem cell22_3027756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_3027756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027756 prefixEnd_3027756 := by exact prefixLift 3027756
  have htrace : WordTrace (prefixWord ++ tailWord_3027756) baseStart_3027756 baseEnd_3027756 := by
    simpa [prefixWord, tailWord_3027756, baseEnd_3027756] using wordTrace_append hprefix tailTrace_3027756
  have hstable : (prefixWord ++ tailWord_3027756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027756).length < 2 ^ (prefixWord ++ tailWord_3027756).sum := by decide
  have hdescent : baseEnd_3027756 < baseStart_3027756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027758 : List Nat := [4, 1, 3, 2, 1, 1, 4, 6]
def baseStart_3027758 : Nat := 118140960795 + 3027758 * 2 ^ 59
def prefixEnd_3027758 : Nat := 4983230072969 + 3 ^ 40 * 3027758 * 2
def baseEnd_3027758 : Nat := 115162604407101490118563

theorem tailTrace_3027758 : CollatzResearch.WordTrace tailWord_3027758 prefixEnd_3027758 115162604407101490118563 := by
  unfold tailWord_3027758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803925820619667592885491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73620937709971560495389285 13803925820619667592885491)
  ·
    refine ⟨20705888730929501389328237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13803925820619667592885491 20705888730929501389328237)
    ·
      refine ⟨7764708274098563020998089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20705888730929501389328237 7764708274098563020998089)
      ·
        refine ⟨5823531205573922265748567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7764708274098563020998089 5823531205573922265748567)
        ·
          refine ⟨8735296808360883398622851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823531205573922265748567 8735296808360883398622851)
          ·
            refine ⟨13102945212541325097934277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735296808360883398622851 13102945212541325097934277)
            ·
              refine ⟨2456802227351498455862677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13102945212541325097934277 2456802227351498455862677)
              ·
                refine ⟨115162604407101490118563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2456802227351498455862677 115162604407101490118563)
                ·
                  rfl

theorem cell22_3027758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_3027758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027758 prefixEnd_3027758 := by exact prefixLift 3027758
  have htrace : WordTrace (prefixWord ++ tailWord_3027758) baseStart_3027758 baseEnd_3027758 := by
    simpa [prefixWord, tailWord_3027758, baseEnd_3027758] using wordTrace_append hprefix tailTrace_3027758
  have hstable : (prefixWord ++ tailWord_3027758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027758).length < 2 ^ (prefixWord ++ tailWord_3027758).sum := by decide
  have hdescent : baseEnd_3027758 < baseStart_3027758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027859 : List Nat := [1, 1, 1, 2, 1, 2, 1, 13]
def baseStart_3027859 : Nat := 118140960795 + 3027859 * 2 ^ 59
def prefixEnd_3027859 : Nat := 4983230072969 + 3 ^ 40 * 3027859 * 2
def baseEnd_3027859 : Nat := 115166446003109201587973

theorem tailTrace_3027859 : CollatzResearch.WordTrace tailWord_3027859 prefixEnd_3027859 115166446003109201587973 := by
  unfold tailWord_3027859
  simp only [CollatzResearch.WordTrace]
  refine ⟨110435090337591434992510631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73623393558394289995007087 110435090337591434992510631)
  ·
    refine ⟨165652635506387152488765947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110435090337591434992510631 165652635506387152488765947)
    ·
      refine ⟨248478953259580728733148921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165652635506387152488765947 248478953259580728733148921)
      ·
        refine ⟨186359214944685546549861691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248478953259580728733148921 186359214944685546549861691)
        ·
          refine ⟨279538822417028319824792537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186359214944685546549861691 279538822417028319824792537)
          ·
            refine ⟨209654116812771239868594403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279538822417028319824792537 209654116812771239868594403)
            ·
              refine ⟨314481175219156859802891605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209654116812771239868594403 314481175219156859802891605)
              ·
                refine ⟨115166446003109201587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 314481175219156859802891605 115166446003109201587973)
                ·
                  rfl

theorem cell22_3027859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_3027859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027859 prefixEnd_3027859 := by exact prefixLift 3027859
  have htrace : WordTrace (prefixWord ++ tailWord_3027859) baseStart_3027859 baseEnd_3027859 := by
    simpa [prefixWord, tailWord_3027859, baseEnd_3027859] using wordTrace_append hprefix tailTrace_3027859
  have hstable : (prefixWord ++ tailWord_3027859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027859).length < 2 ^ (prefixWord ++ tailWord_3027859).sum := by decide
  have hdescent : baseEnd_3027859 < baseStart_3027859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027863 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 2, 3]
def baseStart_3027863 : Nat := 118140960795 + 3027863 * 2 ^ 59
def prefixEnd_3027863 : Nat := 4983230072969 + 3 ^ 40 * 3027863 * 2
def baseEnd_3027863 : Nat := 1036499383309728137191745

theorem tailTrace_3027863 : CollatzResearch.WordTrace tailWord_3027863 prefixEnd_3027863 1036499383309728137191745 := by
  unfold tailWord_3027863
  simp only [CollatzResearch.WordTrace]
  refine ⟨110435236229576943675656243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73623490819717962450437495 110435236229576943675656243)
  ·
    refine ⟨165652854344365415513484365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110435236229576943675656243 165652854344365415513484365)
    ·
      refine ⟨62119820379137030817556637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165652854344365415513484365 62119820379137030817556637)
      ·
        refine ⟨23294932642176386556583739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62119820379137030817556637 23294932642176386556583739)
        ·
          refine ⟨34942398963264579834875609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23294932642176386556583739 34942398963264579834875609)
          ·
            refine ⟨26206799222448434876156707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34942398963264579834875609 26206799222448434876156707)
            ·
              refine ⟨39310198833672652314235061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26206799222448434876156707 39310198833672652314235061)
              ·
                refine ⟨3685331140656811154459537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39310198833672652314235061 3685331140656811154459537)
                ·
                  refine ⟨2763998355492608365844653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3685331140656811154459537 2763998355492608365844653)
                  ·
                    refine ⟨1036499383309728137191745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2763998355492608365844653 1036499383309728137191745)
                    ·
                      rfl

theorem cell22_3027863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_3027863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3027863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3027863 prefixEnd_3027863 := by exact prefixLift 3027863
  have htrace : WordTrace (prefixWord ++ tailWord_3027863) baseStart_3027863 baseEnd_3027863 := by
    simpa [prefixWord, tailWord_3027863, baseEnd_3027863] using wordTrace_append hprefix tailTrace_3027863
  have hstable : (prefixWord ++ tailWord_3027863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027863).length < 2 ^ (prefixWord ++ tailWord_3027863).sum := by decide
  have hdescent : baseEnd_3027863 < baseStart_3027863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028002 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3028002 : Nat := 118140960795 + 3028002 * 2 ^ 59
def prefixEnd_3028002 : Nat := 4983230072969 + 3 ^ 40 * 3028002 * 2
def baseEnd_3028002 : Nat := 1036546965850378107966319

theorem tailTrace_3028002 : CollatzResearch.WordTrace tailWord_3028002 prefixEnd_3028002 1036546965850378107966319 := by
  unfold tailWord_3028002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27610076494018342603741565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73626870650715580276644173 27610076494018342603741565)
  ·
    refine ⟨10353778685256878476403087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27610076494018342603741565 10353778685256878476403087)
    ·
      refine ⟨15530668027885317714604631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353778685256878476403087 15530668027885317714604631)
      ·
        refine ⟨23296002041827976571906947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15530668027885317714604631 23296002041827976571906947)
        ·
          refine ⟨34944003062741964857860421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23296002041827976571906947 34944003062741964857860421)
          ·
            refine ⟨6552000574264118410848829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34944003062741964857860421 6552000574264118410848829)
            ·
              refine ⟨2457000215349044404068311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6552000574264118410848829 2457000215349044404068311)
              ·
                refine ⟨3685500323023566606102467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457000215349044404068311 3685500323023566606102467)
                ·
                  refine ⟨5528250484535349909153701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685500323023566606102467 5528250484535349909153701)
                  ·
                    refine ⟨1036546965850378107966319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528250484535349909153701 1036546965850378107966319)
                    ·
                      rfl

theorem cell22_3028002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3028002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028002 prefixEnd_3028002 := by exact prefixLift 3028002
  have htrace : WordTrace (prefixWord ++ tailWord_3028002) baseStart_3028002 baseEnd_3028002 := by
    simpa [prefixWord, tailWord_3028002, baseEnd_3028002] using wordTrace_append hprefix tailTrace_3028002
  have hstable : (prefixWord ++ tailWord_3028002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028002).length < 2 ^ (prefixWord ++ tailWord_3028002).sum := by decide
  have hdescent : baseEnd_3028002 < baseStart_3028002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028028 : List Nat := [2, 2, 2, 2, 2, 2, 3, 7]
def baseStart_3028028 : Nat := 118140960795 + 3028028 * 2 ^ 59
def prefixEnd_3028028 : Nat := 4983230072969 + 3 ^ 40 * 3028028 * 2
def baseEnd_3028028 : Nat := 115172874020191411868471

theorem tailTrace_3028028 : CollatzResearch.WordTrace tailWord_3028028 prefixEnd_3028028 115172874020191411868471 := by
  unfold tailWord_3028028
  simp only [CollatzResearch.WordTrace]
  refine ⟨55220627136989588427706369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73627502849319451236941825 55220627136989588427706369)
  ·
    refine ⟨41415470352742191320779777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55220627136989588427706369 41415470352742191320779777)
    ·
      refine ⟨31061602764556643490584833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41415470352742191320779777 31061602764556643490584833)
      ·
        refine ⟨23296202073417482617938625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31061602764556643490584833 23296202073417482617938625)
        ·
          refine ⟨17472151555063111963453969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23296202073417482617938625 17472151555063111963453969)
          ·
            refine ⟨13104113666297333972590477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17472151555063111963453969 13104113666297333972590477)
            ·
              refine ⟨4914042624861500239721429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13104113666297333972590477 4914042624861500239721429)
              ·
                refine ⟨115172874020191411868471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4914042624861500239721429 115172874020191411868471)
                ·
                  rfl

theorem cell22_3028028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_3028028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028028 prefixEnd_3028028 := by exact prefixLift 3028028
  have htrace : WordTrace (prefixWord ++ tailWord_3028028) baseStart_3028028 baseEnd_3028028 := by
    simpa [prefixWord, tailWord_3028028, baseEnd_3028028] using wordTrace_append hprefix tailTrace_3028028
  have hstable : (prefixWord ++ tailWord_3028028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028028).length < 2 ^ (prefixWord ++ tailWord_3028028).sum := by decide
  have hdescent : baseEnd_3028028 < baseStart_3028028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028060 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3028060 : Nat := 118140960795 + 3028060 * 2 ^ 59
def prefixEnd_3028060 : Nat := 4983230072969 + 3 ^ 40 * 3028060 * 2
def baseEnd_3028060 : Nat := 1036566820435685290016141

theorem tailTrace_3028060 : CollatzResearch.WordTrace tailWord_3028060 prefixEnd_3028060 1036566820435685290016141 := by
  unfold tailWord_3028060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55221210704931623160288817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73628280939908830880385089 55221210704931623160288817)
  ·
    refine ⟨41415908028698717370216613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55221210704931623160288817 41415908028698717370216613)
    ·
      refine ⟨7765482755381009506915615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41415908028698717370216613 7765482755381009506915615)
      ·
        refine ⟨11648224133071514260373423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765482755381009506915615 11648224133071514260373423)
        ·
          refine ⟨17472336199607271390560135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11648224133071514260373423 17472336199607271390560135)
          ·
            refine ⟨26208504299410907085840203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17472336199607271390560135 26208504299410907085840203)
            ·
              refine ⟨39312756449116360628760305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26208504299410907085840203 39312756449116360628760305)
              ·
                refine ⟨29484567336837270471570229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39312756449116360628760305 29484567336837270471570229)
                ·
                  refine ⟨2764178187828494106709709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29484567336837270471570229 2764178187828494106709709)
                  ·
                    refine ⟨1036566820435685290016141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764178187828494106709709 1036566820435685290016141)
                    ·
                      rfl

theorem cell22_3028060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3028060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028060 prefixEnd_3028060 := by exact prefixLift 3028060
  have htrace : WordTrace (prefixWord ++ tailWord_3028060) baseStart_3028060 baseEnd_3028060 := by
    simpa [prefixWord, tailWord_3028060, baseEnd_3028060] using wordTrace_append hprefix tailTrace_3028060
  have hstable : (prefixWord ++ tailWord_3028060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028060).length < 2 ^ (prefixWord ++ tailWord_3028060).sum := by decide
  have hdescent : baseEnd_3028060 < baseStart_3028060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028062 : List Nat := [4, 4, 1, 1, 1, 2, 9]
def baseStart_3028062 : Nat := 118140960795 + 3028062 * 2 ^ 59
def prefixEnd_3028062 : Nat := 4983230072969 + 3 ^ 40 * 3028062 * 2
def baseEnd_3028062 : Nat := 38391389076909553758005

theorem tailTrace_3028062 : CollatzResearch.WordTrace tailWord_3028062 prefixEnd_3028062 38391389076909553758005 := by
  unfold tailWord_3028062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805311794482000082768805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73628329570570667108100293 13805311794482000082768805)
  ·
    refine ⟨2588495961465375015519151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13805311794482000082768805 2588495961465375015519151)
    ·
      refine ⟨3882743942198062523278727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588495961465375015519151 3882743942198062523278727)
      ·
        refine ⟨5824115913297093784918091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882743942198062523278727 5824115913297093784918091)
        ·
          refine ⟨8736173869945640677377137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824115913297093784918091 8736173869945640677377137)
          ·
            refine ⟨6552130402459230508032853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8736173869945640677377137 6552130402459230508032853)
            ·
              refine ⟨38391389076909553758005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6552130402459230508032853 38391389076909553758005)
              ·
                rfl

theorem cell22_3028062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 9].length) (baseStart_3028062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028062 prefixEnd_3028062 := by exact prefixLift 3028062
  have htrace : WordTrace (prefixWord ++ tailWord_3028062) baseStart_3028062 baseEnd_3028062 := by
    simpa [prefixWord, tailWord_3028062, baseEnd_3028062] using wordTrace_append hprefix tailTrace_3028062
  have hstable : (prefixWord ++ tailWord_3028062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028062).length < 2 ^ (prefixWord ++ tailWord_3028062).sum := by decide
  have hdescent : baseEnd_3028062 < baseStart_3028062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028073 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 7]
def baseStart_3028073 : Nat := 118140960795 + 3028073 * 2 ^ 59
def prefixEnd_3028073 : Nat := 4983230072969 + 3 ^ 40 * 3028073 * 2
def baseEnd_3028073 : Nat := 345523756867119196480367

theorem tailTrace_3028073 : CollatzResearch.WordTrace tailWord_3028073 prefixEnd_3028073 345523756867119196480367 := by
  unfold tailWord_3028073
  simp only [CollatzResearch.WordTrace]
  refine ⟨110442895558816149540800873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73628597039210766360533915 110442895558816149540800873)
  ·
    refine ⟨82832171669112112155600655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110442895558816149540800873 82832171669112112155600655)
    ·
      refine ⟨124248257503668168233400983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82832171669112112155600655 124248257503668168233400983)
      ·
        refine ⟨186372386255502252350101475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124248257503668168233400983 186372386255502252350101475)
        ·
          refine ⟨279558579383253378525152213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186372386255502252350101475 279558579383253378525152213)
          ·
            refine ⟨6552154204295001059183255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 279558579383253378525152213 6552154204295001059183255)
            ·
              refine ⟨9828231306442501588774883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6552154204295001059183255 9828231306442501588774883)
              ·
                refine ⟨14742346959663752383162325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9828231306442501588774883 14742346959663752383162325)
                ·
                  refine ⟨345523756867119196480367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14742346959663752383162325 345523756867119196480367)
                  ·
                    rfl

theorem cell22_3028073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_3028073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028073 prefixEnd_3028073 := by exact prefixLift 3028073
  have htrace : WordTrace (prefixWord ++ tailWord_3028073) baseStart_3028073 baseEnd_3028073 := by
    simpa [prefixWord, tailWord_3028073, baseEnd_3028073] using wordTrace_append hprefix tailTrace_3028073
  have hstable : (prefixWord ++ tailWord_3028073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028073).length < 2 ^ (prefixWord ++ tailWord_3028073).sum := by decide
  have hdescent : baseEnd_3028073 < baseStart_3028073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028077 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3028077 : Nat := 118140960795 + 3028077 * 2 ^ 59
def prefixEnd_3028077 : Nat := 4983230072969 + 3 ^ 40 * 3028077 * 2
def baseEnd_3028077 : Nat := 1036572639883102912341089

theorem tailTrace_3028077 : CollatzResearch.WordTrace tailWord_3028077 prefixEnd_3028077 1036572639883102912341089 := by
  unfold tailWord_3028077
  simp only [CollatzResearch.WordTrace]
  refine ⟨110443041450801658223946485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73628694300534438815964323 110443041450801658223946485)
  ·
    refine ⟨10354035136012655458494983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110443041450801658223946485 10354035136012655458494983)
    ·
      refine ⟨15531052704018983187742475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10354035136012655458494983 15531052704018983187742475)
      ·
        refine ⟨23296579056028474781613713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15531052704018983187742475 23296579056028474781613713)
        ·
          refine ⟨17472434292021356086210285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23296579056028474781613713 17472434292021356086210285)
          ·
            refine ⟨6552162859508008532328857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17472434292021356086210285 6552162859508008532328857)
            ·
              refine ⟨4914122144631006399246643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552162859508008532328857 4914122144631006399246643)
              ·
                refine ⟨7371183216946509598869965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914122144631006399246643 7371183216946509598869965)
                ·
                  refine ⟨2764193706354941099576237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7371183216946509598869965 2764193706354941099576237)
                  ·
                    refine ⟨1036572639883102912341089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764193706354941099576237 1036572639883102912341089)
                    ·
                      rfl

theorem cell22_3028077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3028077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028077 prefixEnd_3028077 := by exact prefixLift 3028077
  have htrace : WordTrace (prefixWord ++ tailWord_3028077) baseStart_3028077 baseEnd_3028077 := by
    simpa [prefixWord, tailWord_3028077, baseEnd_3028077] using wordTrace_append hprefix tailTrace_3028077
  have hstable : (prefixWord ++ tailWord_3028077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028077).length < 2 ^ (prefixWord ++ tailWord_3028077).sum := by decide
  have hdescent : baseEnd_3028077 < baseStart_3028077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028088 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3028088 : Nat := 118140960795 + 3028088 * 2 ^ 59
def prefixEnd_3028088 : Nat := 4983230072969 + 3 ^ 40 * 3028088 * 2
def baseEnd_3028088 : Nat := 1036576405407902550316055

theorem tailTrace_3028088 : CollatzResearch.WordTrace tailWord_3028088 prefixEnd_3028088 1036576405407902550316055 := by
  unfold tailWord_3028088
  simp only [CollatzResearch.WordTrace]
  refine ⟨55221721326880903551298459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73628961769174538068397945 55221721326880903551298459)
  ·
    refine ⟨82832581990321355326947689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55221721326880903551298459 82832581990321355326947689)
    ·
      refine ⟨62124436492741016495210767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82832581990321355326947689 62124436492741016495210767)
      ·
        refine ⟨93186654739111524742816151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62124436492741016495210767 93186654739111524742816151)
        ·
          refine ⟨139779982108667287114224227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93186654739111524742816151 139779982108667287114224227)
          ·
            refine ⟨209669973163000930671336341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139779982108667287114224227 209669973163000930671336341)
            ·
              refine ⟨9828279992015668625218891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209669973163000930671336341 9828279992015668625218891)
              ·
                refine ⟨14742419988023502937828337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9828279992015668625218891 14742419988023502937828337)
                ·
                  refine ⟨11056814991017627203371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14742419988023502937828337 11056814991017627203371253)
                  ·
                    refine ⟨1036576405407902550316055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11056814991017627203371253 1036576405407902550316055)
                    ·
                      rfl

theorem cell22_3028088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3028088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028088 prefixEnd_3028088 := by exact prefixLift 3028088
  have htrace : WordTrace (prefixWord ++ tailWord_3028088) baseStart_3028088 baseEnd_3028088 := by
    simpa [prefixWord, tailWord_3028088, baseEnd_3028088] using wordTrace_append hprefix tailTrace_3028088
  have hstable : (prefixWord ++ tailWord_3028088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028088).length < 2 ^ (prefixWord ++ tailWord_3028088).sum := by decide
  have hdescent : baseEnd_3028088 < baseStart_3028088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028141 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3028141 : Nat := 118140960795 + 3028141 * 2 ^ 59
def prefixEnd_3028141 : Nat := 4983230072969 + 3 ^ 40 * 3028141 * 2
def baseEnd_3028141 : Nat := 345531516130342692913631

theorem tailTrace_3028141 : CollatzResearch.WordTrace tailWord_3028141 prefixEnd_3028141 345531516130342692913631 := by
  unfold tailWord_3028141
  simp only [CollatzResearch.WordTrace]
  refine ⟨110445375722569797154276277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73630250481713198102850851 110445375722569797154276277)
  ·
    refine ⟨10354253973990918483213401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110445375722569797154276277 10354253973990918483213401)
    ·
      refine ⟨7765690480493188862410051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10354253973990918483213401 7765690480493188862410051)
      ·
        refine ⟨11648535720739783293615077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765690480493188862410051 11648535720739783293615077)
        ·
          refine ⟨2184100447638709367552827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11648535720739783293615077 2184100447638709367552827)
          ·
            refine ⟨3276150671458064051329241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184100447638709367552827 3276150671458064051329241)
            ·
              refine ⟨2457113003593548038496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276150671458064051329241 2457113003593548038496931)
              ·
                refine ⟨3685669505390322057745397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457113003593548038496931 3685669505390322057745397)
                ·
                  refine ⟨345531516130342692913631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685669505390322057745397 345531516130342692913631)
                  ·
                    rfl

theorem cell22_3028141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3028141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028141 prefixEnd_3028141 := by exact prefixLift 3028141
  have htrace : WordTrace (prefixWord ++ tailWord_3028141) baseStart_3028141 baseEnd_3028141 := by
    simpa [prefixWord, tailWord_3028141, baseEnd_3028141] using wordTrace_append hprefix tailTrace_3028141
  have hstable : (prefixWord ++ tailWord_3028141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028141).length < 2 ^ (prefixWord ++ tailWord_3028141).sum := by decide
  have hdescent : baseEnd_3028141 < baseStart_3028141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028180 : List Nat := [2, 4, 1, 4, 11]
def baseStart_3028180 : Nat := 118140960795 + 3028180 * 2 ^ 59
def prefixEnd_3028180 : Nat := 4983230072969 + 3 ^ 40 * 3028180 * 2
def baseEnd_3028180 : Nat := 4265876127111296201711

theorem tailTrace_3028180 : CollatzResearch.WordTrace tailWord_3028180 prefixEnd_3028180 4265876127111296201711 := by
  unfold tailWord_3028180
  simp only [CollatzResearch.WordTrace]
  refine ⟨55223399084714253407472997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73631198779619004543297329 55223399084714253407472997)
  ·
    refine ⟨10354387328383922513901187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55223399084714253407472997 10354387328383922513901187)
    ·
      refine ⟨15531580992575883770851781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10354387328383922513901187 15531580992575883770851781)
      ·
        refine ⟨2912171436107978207034709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15531580992575883770851781 2912171436107978207034709)
        ·
          refine ⟨4265876127111296201711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2912171436107978207034709 4265876127111296201711)
          ·
            rfl

theorem cell22_3028180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 11].length) (baseStart_3028180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028180 prefixEnd_3028180 := by exact prefixLift 3028180
  have htrace : WordTrace (prefixWord ++ tailWord_3028180) baseStart_3028180 baseEnd_3028180 := by
    simpa [prefixWord, tailWord_3028180, baseEnd_3028180] using wordTrace_append hprefix tailTrace_3028180
  have hstable : (prefixWord ++ tailWord_3028180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028180).length < 2 ^ (prefixWord ++ tailWord_3028180).sum := by decide
  have hdescent : baseEnd_3028180 < baseStart_3028180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028184 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_3028184 : Nat := 118140960795 + 3028184 * 2 ^ 59
def prefixEnd_3028184 : Nat := 4983230072969 + 3 ^ 40 * 3028184 * 2
def baseEnd_3028184 : Nat := 1036609268169790299915761

theorem tailTrace_3028184 : CollatzResearch.WordTrace tailWord_3028184 prefixEnd_3028184 1036609268169790299915761 := by
  unfold tailWord_3028184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55223472030707007749045803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73631296040942676998727737 55223472030707007749045803)
  ·
    refine ⟨82835208046060511623568705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55223472030707007749045803 82835208046060511623568705)
    ·
      refine ⟨62126406034545383717676529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82835208046060511623568705 62126406034545383717676529)
      ·
        refine ⟨46594804525909037788257397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62126406034545383717676529 46594804525909037788257397)
        ·
          refine ⟨4368262924303972292649131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46594804525909037788257397 4368262924303972292649131)
          ·
            refine ⟨6552394386455958438973697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368262924303972292649131 6552394386455958438973697)
            ·
              refine ⟨4914295789841968829230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552394386455958438973697 4914295789841968829230273)
              ·
                refine ⟨3685721842381476621922705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914295789841968829230273 3685721842381476621922705)
                ·
                  refine ⟨2764291381786107466442029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3685721842381476621922705 2764291381786107466442029)
                  ·
                    refine ⟨1036609268169790299915761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764291381786107466442029 1036609268169790299915761)
                    ·
                      rfl

theorem cell22_3028184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_3028184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028184 prefixEnd_3028184 := by exact prefixLift 3028184
  have htrace : WordTrace (prefixWord ++ tailWord_3028184) baseStart_3028184 baseEnd_3028184 := by
    simpa [prefixWord, tailWord_3028184, baseEnd_3028184] using wordTrace_append hprefix tailTrace_3028184
  have hstable : (prefixWord ++ tailWord_3028184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028184).length < 2 ^ (prefixWord ++ tailWord_3028184).sum := by decide
  have hdescent : baseEnd_3028184 < baseStart_3028184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028197 : List Nat := [1, 3, 1, 4, 3, 2, 1, 7]
def baseStart_3028197 : Nat := 118140960795 + 3028197 * 2 ^ 59
def prefixEnd_3028197 : Nat := 4983230072969 + 3 ^ 40 * 3028197 * 2
def baseEnd_3028197 : Nat := 115179302037273622148969

theorem tailTrace_3028197 : CollatzResearch.WordTrace tailWord_3028197 prefixEnd_3028197 115179302037273622148969 := by
  unfold tailWord_3028197
  simp only [CollatzResearch.WordTrace]
  refine ⟨110447418210366918718314845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73631612140244612478876563 110447418210366918718314845)
  ·
    refine ⟨41417781828887594519368067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110447418210366918718314845 41417781828887594519368067)
    ·
      refine ⟨62126672743331391779052101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41417781828887594519368067 62126672743331391779052101)
      ·
        refine ⟨11648751139374635958572269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62126672743331391779052101 11648751139374635958572269)
        ·
          refine ⟨4368281677265488484464601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11648751139374635958572269 4368281677265488484464601)
          ·
            refine ⟨3276211257949116363348451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4368281677265488484464601 3276211257949116363348451)
            ·
              refine ⟨4914316886923674545022677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276211257949116363348451 4914316886923674545022677)
              ·
                refine ⟨115179302037273622148969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4914316886923674545022677 115179302037273622148969)
                ·
                  rfl

theorem cell22_3028197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 7].length) (baseStart_3028197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028197 prefixEnd_3028197 := by exact prefixLift 3028197
  have htrace : WordTrace (prefixWord ++ tailWord_3028197) baseStart_3028197 baseEnd_3028197 := by
    simpa [prefixWord, tailWord_3028197, baseEnd_3028197] using wordTrace_append hprefix tailTrace_3028197
  have hstable : (prefixWord ++ tailWord_3028197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028197).length < 2 ^ (prefixWord ++ tailWord_3028197).sum := by decide
  have hdescent : baseEnd_3028197 < baseStart_3028197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028208 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_3028208 : Nat := 118140960795 + 3028208 * 2 ^ 59
def prefixEnd_3028208 : Nat := 4983230072969 + 3 ^ 40 * 3028208 * 2
def baseEnd_3028208 : Nat := 345539161286754079105229

theorem tailTrace_3028208 : CollatzResearch.WordTrace tailWord_3028208 prefixEnd_3028208 345539161286754079105229 := by
  unfold tailWord_3028208
  simp only [CollatzResearch.WordTrace]
  refine ⟨55223909706663533798482639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73631879608884711731310185 55223909706663533798482639)
  ·
    refine ⟨82835864559995300697723959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55223909706663533798482639 82835864559995300697723959)
    ·
      refine ⟨124253796839992951046585939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82835864559995300697723959 124253796839992951046585939)
      ·
        refine ⟨186380695259989426569878909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124253796839992951046585939 186380695259989426569878909)
        ·
          refine ⟨69892760722496034963704591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186380695259989426569878909 69892760722496034963704591)
          ·
            refine ⟨104839141083744052445556887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69892760722496034963704591 104839141083744052445556887)
            ·
              refine ⟨157258711625616078668335331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104839141083744052445556887 157258711625616078668335331)
              ·
                refine ⟨235888067438424118002502997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157258711625616078668335331 235888067438424118002502997)
                ·
                  refine ⟨345539161286754079105229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 235888067438424118002502997 345539161286754079105229)
                  ·
                    rfl

theorem cell22_3028208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_3028208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028208 prefixEnd_3028208 := by exact prefixLift 3028208
  have htrace : WordTrace (prefixWord ++ tailWord_3028208) baseStart_3028208 baseEnd_3028208 := by
    simpa [prefixWord, tailWord_3028208, baseEnd_3028208] using wordTrace_append hprefix tailTrace_3028208
  have hstable : (prefixWord ++ tailWord_3028208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028208).length < 2 ^ (prefixWord ++ tailWord_3028208).sum := by decide
  have hdescent : baseEnd_3028208 < baseStart_3028208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028229 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_3028229 : Nat := 118140960795 + 3028229 * 2 ^ 59
def prefixEnd_3028229 : Nat := 4983230072969 + 3 ^ 40 * 3028229 * 2
def baseEnd_3028229 : Nat := 1036624672589425182540623

theorem tailTrace_3028229 : CollatzResearch.WordTrace tailWord_3028229 prefixEnd_3028229 1036624672589425182540623 := by
  unfold tailWord_3028229
  simp only [CollatzResearch.WordTrace]
  refine ⟨110448585346250988183479741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73632390230833992122319827 110448585346250988183479741)
  ·
    refine ⟨41418219504844120568804903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110448585346250988183479741 41418219504844120568804903)
    ·
      refine ⟨62127329257266180853207355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41418219504844120568804903 62127329257266180853207355)
      ·
        refine ⟨93190993885899271279811033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62127329257266180853207355 93190993885899271279811033)
        ·
          refine ⟨69893245414424453459858275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93190993885899271279811033 69893245414424453459858275)
          ·
            refine ⟨104839868121636680189787413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69893245414424453459858275 104839868121636680189787413)
            ·
              refine ⟨4914368818201719383896285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104839868121636680189787413 4914368818201719383896285)
              ·
                refine ⟨1842888306825644768961107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914368818201719383896285 1842888306825644768961107)
                ·
                  refine ⟨2764332460238467153441661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842888306825644768961107 2764332460238467153441661)
                  ·
                    refine ⟨1036624672589425182540623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764332460238467153441661 1036624672589425182540623)
                    ·
                      rfl

theorem cell22_3028229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_3028229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028229 prefixEnd_3028229 := by exact prefixLift 3028229
  have htrace : WordTrace (prefixWord ++ tailWord_3028229) baseStart_3028229 baseEnd_3028229 := by
    simpa [prefixWord, tailWord_3028229, baseEnd_3028229] using wordTrace_append hprefix tailTrace_3028229
  have hstable : (prefixWord ++ tailWord_3028229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028229).length < 2 ^ (prefixWord ++ tailWord_3028229).sum := by decide
  have hdescent : baseEnd_3028229 < baseStart_3028229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028272 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_3028272 : Nat := 118140960795 + 3028272 * 2 ^ 59
def prefixEnd_3028272 : Nat := 4983230072969 + 3 ^ 40 * 3028272 * 2
def baseEnd_3028272 : Nat := 1036639392368187403715491

theorem tailTrace_3028272 : CollatzResearch.WordTrace tailWord_3028272 prefixEnd_3028272 1036639392368187403715491 := by
  unfold tailWord_3028272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55225076842547603263647535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73633435790063471018196713 55225076842547603263647535)
  ·
    refine ⟨82837615263821404895471303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55225076842547603263647535 82837615263821404895471303)
    ·
      refine ⟨124256422895732107343206955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82837615263821404895471303 124256422895732107343206955)
      ·
        refine ⟨186384634343598161014810433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124256422895732107343206955 186384634343598161014810433)
        ·
          refine ⟨139788475757698620761107825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186384634343598161014810433 139788475757698620761107825)
          ·
            refine ⟨104841356818273965570830869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139788475757698620761107825 104841356818273965570830869)
            ·
              refine ⟨4914438600856592136132697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104841356818273965570830869 4914438600856592136132697)
              ·
                refine ⟨3685828950642444102099523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914438600856592136132697 3685828950642444102099523)
                ·
                  refine ⟨5528743425963666153149285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685828950642444102099523 5528743425963666153149285)
                  ·
                    refine ⟨1036639392368187403715491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528743425963666153149285 1036639392368187403715491)
                    ·
                      rfl

theorem cell22_3028272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_3028272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028272 prefixEnd_3028272 := by exact prefixLift 3028272
  have htrace : WordTrace (prefixWord ++ tailWord_3028272) baseStart_3028272 baseEnd_3028272 := by
    simpa [prefixWord, tailWord_3028272, baseEnd_3028272] using wordTrace_append hprefix tailTrace_3028272
  have hstable : (prefixWord ++ tailWord_3028272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028272).length < 2 ^ (prefixWord ++ tailWord_3028272).sum := by decide
  have hdescent : baseEnd_3028272 < baseStart_3028272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028289 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3028289 : Nat := 118140960795 + 3028289 * 2 ^ 59
def prefixEnd_3028289 : Nat := 4983230072969 + 3 ^ 40 * 3028289 * 2
def baseEnd_3028289 : Nat := 1036645211815605026040439

theorem tailTrace_3028289 : CollatzResearch.WordTrace tailWord_3028289 prefixEnd_3028289 1036645211815605026040439 := by
  unfold tailWord_3028289
  simp only [CollatzResearch.WordTrace]
  refine ⟨110450773726033618430663921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73633849150689078953775947 110450773726033618430663921)
  ·
    refine ⟨82838080294525213822997941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110450773726033618430663921 82838080294525213822997941)
    ·
      refine ⟨7766070027611738795906057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82838080294525213822997941 7766070027611738795906057)
      ·
        refine ⟨5824552520708804096929543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7766070027611738795906057 5824552520708804096929543)
        ·
          refine ⟨8736828781063206145394315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824552520708804096929543 8736828781063206145394315)
          ·
            refine ⟨13105243171594809218091473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736828781063206145394315 13105243171594809218091473)
            ·
              refine ⟨9828932378696106913568605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13105243171594809218091473 9828932378696106913568605)
              ·
                refine ⟨3685849642011040092588227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9828932378696106913568605 3685849642011040092588227)
                ·
                  refine ⟨5528774463016560138882341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685849642011040092588227 5528774463016560138882341)
                  ·
                    refine ⟨1036645211815605026040439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528774463016560138882341 1036645211815605026040439)
                    ·
                      rfl

theorem cell22_3028289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3028289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028289 prefixEnd_3028289 := by exact prefixLift 3028289
  have htrace : WordTrace (prefixWord ++ tailWord_3028289) baseStart_3028289 baseEnd_3028289 := by
    simpa [prefixWord, tailWord_3028289, baseEnd_3028289] using wordTrace_append hprefix tailTrace_3028289
  have hstable : (prefixWord ++ tailWord_3028289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028289).length < 2 ^ (prefixWord ++ tailWord_3028289).sum := by decide
  have hdescent : baseEnd_3028289 < baseStart_3028289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028302 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3028302 : Nat := 118140960795 + 3028302 * 2 ^ 59
def prefixEnd_3028302 : Nat := 4983230072969 + 3 ^ 40 * 3028302 * 2
def baseEnd_3028302 : Nat := 1036649661981277325465399

theorem tailTrace_3028302 : CollatzResearch.WordTrace tailWord_3028302 prefixEnd_3028302 1036649661981277325465399 := by
  unfold tailWord_3028302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806405984373315206360895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73634165249991014433924773 13806405984373315206360895)
  ·
    refine ⟨20709608976559972809541343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13806405984373315206360895 20709608976559972809541343)
    ·
      refine ⟨31064413464839959214312015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20709608976559972809541343 31064413464839959214312015)
      ·
        refine ⟨46596620197259938821468023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31064413464839959214312015 46596620197259938821468023)
        ·
          refine ⟨69894930295889908232202035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46596620197259938821468023 69894930295889908232202035)
          ·
            refine ⟨104842395443834862348303053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69894930295889908232202035 104842395443834862348303053)
            ·
              refine ⟨39315898291438073380613645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104842395443834862348303053 39315898291438073380613645)
              ·
                refine ⟨14743461859289277517730117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39315898291438073380613645 14743461859289277517730117)
                ·
                  refine ⟨2764399098616739534574397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14743461859289277517730117 2764399098616739534574397)
                  ·
                    refine ⟨1036649661981277325465399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764399098616739534574397 1036649661981277325465399)
                    ·
                      rfl

theorem cell22_3028302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3028302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028302 prefixEnd_3028302 := by exact prefixLift 3028302
  have htrace : WordTrace (prefixWord ++ tailWord_3028302) baseStart_3028302 baseEnd_3028302 := by
    simpa [prefixWord, tailWord_3028302, baseEnd_3028302] using wordTrace_append hprefix tailTrace_3028302
  have hstable : (prefixWord ++ tailWord_3028302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028302).length < 2 ^ (prefixWord ++ tailWord_3028302).sum := by decide
  have hdescent : baseEnd_3028302 < baseStart_3028302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028304 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_3028304 : Nat := 118140960795 + 3028304 * 2 ^ 59
def prefixEnd_3028304 : Nat := 4983230072969 + 3 ^ 40 * 3028304 * 2
def baseEnd_3028304 : Nat := 345550115540716662305131

theorem tailTrace_3028304 : CollatzResearch.WordTrace tailWord_3028304 prefixEnd_3028304 345550115540716662305131 := by
  unfold tailWord_3028304
  simp only [CollatzResearch.WordTrace]
  refine ⟨55225660410489637996229983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73634213880652850661639977 55225660410489637996229983)
  ·
    refine ⟨82838490615734456994344975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55225660410489637996229983 82838490615734456994344975)
    ·
      refine ⟨124257735923601685491517463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82838490615734456994344975 124257735923601685491517463)
      ·
        refine ⟨186386603885402528237276195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124257735923601685491517463 186386603885402528237276195)
        ·
          refine ⟨279579905828103792355914293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186386603885402528237276195 279579905828103792355914293)
          ·
            refine ⟨26210616171384730533366965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279579905828103792355914293 26210616171384730533366965)
            ·
              refine ⟨2457245266067318487503153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26210616171384730533366965 2457245266067318487503153)
              ·
                refine ⟨1842933949550488865627365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457245266067318487503153 1842933949550488865627365)
                ·
                  refine ⟨345550115540716662305131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842933949550488865627365 345550115540716662305131)
                  ·
                    rfl

theorem cell22_3028304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_3028304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028304 prefixEnd_3028304 := by exact prefixLift 3028304
  have htrace : WordTrace (prefixWord ++ tailWord_3028304) baseStart_3028304 baseEnd_3028304 := by
    simpa [prefixWord, tailWord_3028304, baseEnd_3028304] using wordTrace_append hprefix tailTrace_3028304
  have hstable : (prefixWord ++ tailWord_3028304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028304).length < 2 ^ (prefixWord ++ tailWord_3028304).sum := by decide
  have hdescent : baseEnd_3028304 < baseStart_3028304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028366 : List Nat := [4, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3028366 : Nat := 118140960795 + 3028366 * 2 ^ 59
def prefixEnd_3028366 : Nat := 4983230072969 + 3 ^ 40 * 3028366 * 2
def baseEnd_3028366 : Nat := 115185730054355832429467

theorem tailTrace_3028366 : CollatzResearch.WordTrace tailWord_3028366 prefixEnd_3028366 115185730054355832429467 := by
  unfold tailWord_3028366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806697768344332572652119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73635721431169773720811301 13806697768344332572652119)
  ·
    refine ⟨20710046652516498858978179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13806697768344332572652119 20710046652516498858978179)
    ·
      refine ⟨31065069978774748288467269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20710046652516498858978179 31065069978774748288467269)
      ·
        refine ⟨5824700621020265304087613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31065069978774748288467269 5824700621020265304087613)
        ·
          refine ⟨2184262732882599489032855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5824700621020265304087613 2184262732882599489032855)
          ·
            refine ⟨3276394099323899233549283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184262732882599489032855 3276394099323899233549283)
            ·
              refine ⟨4914591148985848850323925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276394099323899233549283 4914591148985848850323925)
              ·
                refine ⟨115185730054355832429467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4914591148985848850323925 115185730054355832429467)
                ·
                  rfl

theorem cell22_3028366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3028366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028366 prefixEnd_3028366 := by exact prefixLift 3028366
  have htrace : WordTrace (prefixWord ++ tailWord_3028366) baseStart_3028366 baseEnd_3028366 := by
    simpa [prefixWord, tailWord_3028366, baseEnd_3028366] using wordTrace_append hprefix tailTrace_3028366
  have hstable : (prefixWord ++ tailWord_3028366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028366).length < 2 ^ (prefixWord ++ tailWord_3028366).sum := by decide
  have hdescent : baseEnd_3028366 < baseStart_3028366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028377 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 5]
def baseStart_3028377 : Nat := 118140960795 + 3028377 * 2 ^ 59
def prefixEnd_3028377 : Nat := 4983230072969 + 3 ^ 40 * 3028377 * 2
def baseEnd_3028377 : Nat := 345558445338000709946723

theorem tailTrace_3028377 : CollatzResearch.WordTrace tailWord_3028377 prefixEnd_3028377 345558445338000709946723 := by
  unfold tailWord_3028377
  simp only [CollatzResearch.WordTrace]
  refine ⟨110453983349714809459867385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73635988899809872973244923 110453983349714809459867385)
  ·
    refine ⟨82840487512286107094900539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110453983349714809459867385 82840487512286107094900539)
    ·
      refine ⟨124260731268429160642350809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82840487512286107094900539 124260731268429160642350809)
      ·
        refine ⟨93195548451321870481763107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124260731268429160642350809 93195548451321870481763107)
        ·
          refine ⟨139793322676982805722644661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93195548451321870481763107 139793322676982805722644661)
          ·
            refine ⟨13105624000967138036497937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139793322676982805722644661 13105624000967138036497937)
            ·
              refine ⟨9829218000725353527373453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13105624000967138036497937 9829218000725353527373453)
              ·
                refine ⟨3685956750272007572765045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9829218000725353527373453 3685956750272007572765045)
                ·
                  refine ⟨345558445338000709946723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685956750272007572765045 345558445338000709946723)
                  ·
                    rfl

theorem cell22_3028377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_3028377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028377 prefixEnd_3028377 := by exact prefixLift 3028377
  have htrace : WordTrace (prefixWord ++ tailWord_3028377) baseStart_3028377 baseEnd_3028377 := by
    simpa [prefixWord, tailWord_3028377, baseEnd_3028377] using wordTrace_append hprefix tailTrace_3028377
  have hstable : (prefixWord ++ tailWord_3028377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028377).length < 2 ^ (prefixWord ++ tailWord_3028377).sum := by decide
  have hdescent : baseEnd_3028377 < baseStart_3028377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_3028452 : Nat := 118140960795 + 3028452 * 2 ^ 59
def prefixEnd_3028452 : Nat := 4983230072969 + 3 ^ 40 * 3028452 * 2
def baseEnd_3028452 : Nat := 1036701010046726934214939

theorem tailTrace_3028452 : CollatzResearch.WordTrace tailWord_3028452 prefixEnd_3028452 1036701010046726934214939 := by
  unfold tailWord_3028452
  simp only [CollatzResearch.WordTrace]
  refine ⟨55228359412221548634423805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73637812549628731512565073 55228359412221548634423805)
  ·
    refine ⟨20710634779583080737908927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55228359412221548634423805 20710634779583080737908927)
    ·
      refine ⟨31065952169374621106863391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20710634779583080737908927 31065952169374621106863391)
      ·
        refine ⟨46598928254061931660295087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31065952169374621106863391 46598928254061931660295087)
        ·
          refine ⟨69898392381092897490442631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46598928254061931660295087 69898392381092897490442631)
          ·
            refine ⟨104847588571639346235663947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69898392381092897490442631 104847588571639346235663947)
            ·
              refine ⟨157271382857459019353495921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104847588571639346235663947 157271382857459019353495921)
              ·
                refine ⟨117953537143094264515121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157271382857459019353495921 117953537143094264515121941)
                ·
                  refine ⟨5529072053582543649146341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117953537143094264515121941 5529072053582543649146341)
                  ·
                    refine ⟨1036701010046726934214939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529072053582543649146341 1036701010046726934214939)
                    ·
                      rfl

theorem cell22_3028452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_3028452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028452 prefixEnd_3028452 := by exact prefixLift 3028452
  have htrace : WordTrace (prefixWord ++ tailWord_3028452) baseStart_3028452 baseEnd_3028452 := by
    simpa [prefixWord, tailWord_3028452, baseEnd_3028452] using wordTrace_append hprefix tailTrace_3028452
  have hstable : (prefixWord ++ tailWord_3028452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028452).length < 2 ^ (prefixWord ++ tailWord_3028452).sum := by decide
  have hdescent : baseEnd_3028452 < baseStart_3028452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028533 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3028533 : Nat := 118140960795 + 3028533 * 2 ^ 59
def prefixEnd_3028533 : Nat := 4983230072969 + 3 ^ 40 * 3028533 * 2
def baseEnd_3028533 : Nat := 1036728738002069722939691

theorem tailTrace_3028533 : CollatzResearch.WordTrace tailWord_3028533 prefixEnd_3028533 1036728738002069722939691 := by
  unfold tailWord_3028533
  simp only [CollatzResearch.WordTrace]
  refine ⟨110459673137149648102546253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73639782091433098735030835 110459673137149648102546253)
  ·
    refine ⟨41422377426431118038454845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110459673137149648102546253 41422377426431118038454845)
    ·
      refine ⟨15533391534911669264420567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41422377426431118038454845 15533391534911669264420567)
      ·
        refine ⟨23300087302367503896630851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15533391534911669264420567 23300087302367503896630851)
        ·
          refine ⟨34950130953551255844946277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23300087302367503896630851 34950130953551255844946277)
          ·
            refine ⟨6553149553790860470927427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34950130953551255844946277 6553149553790860470927427)
            ·
              refine ⟨9829724330686290706391141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553149553790860470927427 9829724330686290706391141)
              ·
                refine ⟨1843073312003679507448339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9829724330686290706391141 1843073312003679507448339)
                ·
                  refine ⟨2764609968005519261172509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843073312003679507448339 2764609968005519261172509)
                  ·
                    refine ⟨1036728738002069722939691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764609968005519261172509 1036728738002069722939691)
                    ·
                      rfl

theorem cell22_3028533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3028533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028533 prefixEnd_3028533 := by exact prefixLift 3028533
  have htrace : WordTrace (prefixWord ++ tailWord_3028533) baseStart_3028533 baseEnd_3028533 := by
    simpa [prefixWord, tailWord_3028533, baseEnd_3028533] using wordTrace_append hprefix tailTrace_3028533
  have hstable : (prefixWord ++ tailWord_3028533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028533).length < 2 ^ (prefixWord ++ tailWord_3028533).sum := by decide
  have hdescent : baseEnd_3028533 < baseStart_3028533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028550 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3028550 : Nat := 118140960795 + 3028550 * 2 ^ 59
def prefixEnd_3028550 : Nat := 4983230072969 + 3 ^ 40 * 3028550 * 2
def baseEnd_3028550 : Nat := 1036734557449487345264639

theorem tailTrace_3028550 : CollatzResearch.WordTrace tailWord_3028550 prefixEnd_3028550 1036734557449487345264639 := by
  unfold tailWord_3028550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451884161815251875184847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73640195452058706670610069 3451884161815251875184847)
  ·
    refine ⟨5177826242722877812777271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3451884161815251875184847 5177826242722877812777271)
    ·
      refine ⟨7766739364084316719165907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177826242722877812777271 7766739364084316719165907)
      ·
        refine ⟨11650109046126475078748861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766739364084316719165907 11650109046126475078748861)
        ·
          refine ⟨4368790892297428154530823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11650109046126475078748861 4368790892297428154530823)
          ·
            refine ⟨6553186338446142231796235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368790892297428154530823 6553186338446142231796235)
            ·
              refine ⟨9829779507669213347694353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553186338446142231796235 9829779507669213347694353)
              ·
                refine ⟨7372334630751910010770765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9829779507669213347694353 7372334630751910010770765)
                ·
                  refine ⟨2764625486531966254039037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7372334630751910010770765 2764625486531966254039037)
                  ·
                    refine ⟨1036734557449487345264639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764625486531966254039037 1036734557449487345264639)
                    ·
                      rfl

theorem cell22_3028550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3028550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028550 prefixEnd_3028550 := by exact prefixLift 3028550
  have htrace : WordTrace (prefixWord ++ tailWord_3028550) baseStart_3028550 baseEnd_3028550 := by
    simpa [prefixWord, tailWord_3028550, baseEnd_3028550] using wordTrace_append hprefix tailTrace_3028550
  have hstable : (prefixWord ++ tailWord_3028550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028550).length < 2 ^ (prefixWord ++ tailWord_3028550).sum := by decide
  have hdescent : baseEnd_3028550 < baseStart_3028550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028559 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 1, 4]
def baseStart_3028559 : Nat := 118140960795 + 3028559 * 2 ^ 59
def prefixEnd_3028559 : Nat := 4983230072969 + 3 ^ 40 * 3028559 * 2
def baseEnd_3028559 : Nat := 1036737638333414321789611

theorem tailTrace_3028559 : CollatzResearch.WordTrace tailWord_3028559 prefixEnd_3028559 1036737638333414321789611 := by
  unfold tailWord_3028559
  simp only [CollatzResearch.WordTrace]
  refine ⟨110460621435055454542992731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73640414290036969695328487 110460621435055454542992731)
  ·
    refine ⟨165690932152583181814489097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110460621435055454542992731 165690932152583181814489097)
    ·
      refine ⟨124268199114437386360866823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165690932152583181814489097 124268199114437386360866823)
      ·
        refine ⟨186402298671656079541300235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124268199114437386360866823 186402298671656079541300235)
        ·
          refine ⟨279603448007484119311950353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186402298671656079541300235 279603448007484119311950353)
          ·
            refine ⟨209702586005613089483962765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279603448007484119311950353 209702586005613089483962765)
            ·
              refine ⟨78638469752104908556486037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209702586005613089483962765 78638469752104908556486037)
              ·
                refine ⟨3686178269629917588585283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78638469752104908556486037 3686178269629917588585283)
                ·
                  refine ⟨5529267404444876382877925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686178269629917588585283 5529267404444876382877925)
                  ·
                    refine ⟨1036737638333414321789611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529267404444876382877925 1036737638333414321789611)
                    ·
                      rfl

theorem cell22_3028559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_3028559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028559 prefixEnd_3028559 := by exact prefixLift 3028559
  have htrace : WordTrace (prefixWord ++ tailWord_3028559) baseStart_3028559 baseEnd_3028559 := by
    simpa [prefixWord, tailWord_3028559, baseEnd_3028559] using wordTrace_append hprefix tailTrace_3028559
  have hstable : (prefixWord ++ tailWord_3028559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028559).length < 2 ^ (prefixWord ++ tailWord_3028559).sum := by decide
  have hdescent : baseEnd_3028559 < baseStart_3028559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028636 : List Nat := [2, 2, 3, 2, 3, 2, 8]
def baseStart_3028636 : Nat := 118140960795 + 3028636 * 2 ^ 59
def prefixEnd_3028636 : Nat := 4983230072969 + 3 ^ 40 * 3028636 * 2
def baseEnd_3028636 : Nat := 38398666555815251393125

theorem tailTrace_3028636 : CollatzResearch.WordTrace tailWord_3028636 prefixEnd_3028636 38398666555815251393125 := by
  unfold tailWord_3028636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55231714927888248346772881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73642286570517664462363841 55231714927888248346772881)
  ·
    refine ⟨41423786195916186260079661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55231714927888248346772881 41423786195916186260079661)
    ·
      refine ⟨15533919823468569847529873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41423786195916186260079661 15533919823468569847529873)
      ·
        refine ⟨11650439867601427385647405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15533919823468569847529873 11650439867601427385647405)
        ·
          refine ⟨4368914950350535269617777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11650439867601427385647405 4368914950350535269617777)
          ·
            refine ⟨3276686212762901452213333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4368914950350535269617777 3276686212762901452213333)
            ·
              refine ⟨38398666555815251393125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3276686212762901452213333 38398666555815251393125)
              ·
                rfl

theorem cell22_3028636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 8].length) (baseStart_3028636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028636 prefixEnd_3028636 := by exact prefixLift 3028636
  have htrace : WordTrace (prefixWord ++ tailWord_3028636) baseStart_3028636 baseEnd_3028636 := by
    simpa [prefixWord, tailWord_3028636, baseEnd_3028636] using wordTrace_append hprefix tailTrace_3028636
  have hstable : (prefixWord ++ tailWord_3028636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028636).length < 2 ^ (prefixWord ++ tailWord_3028636).sum := by decide
  have hdescent : baseEnd_3028636 < baseStart_3028636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028638 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3028638 : Nat := 118140960795 + 3028638 * 2 ^ 59
def prefixEnd_3028638 : Nat := 4983230072969 + 3 ^ 40 * 3028638 * 2
def baseEnd_3028638 : Nat := 1036764681647884449064369

theorem tailTrace_3028638 : CollatzResearch.WordTrace tailWord_3028638 prefixEnd_3028638 1036764681647884449064369 := by
  unfold tailWord_3028638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807937850221156379389821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73642335201179500690079045 13807937850221156379389821)
  ·
    refine ⟨5177976693832933642271183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13807937850221156379389821 5177976693832933642271183)
    ·
      refine ⟨7766965040749400463406775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177976693832933642271183 7766965040749400463406775)
      ·
        refine ⟨11650447561124100695110163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766965040749400463406775 11650447561124100695110163)
        ·
          refine ⟨17475671341686151042665245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11650447561124100695110163 17475671341686151042665245)
          ·
            refine ⟨6553376753132306640999467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17475671341686151042665245 6553376753132306640999467)
            ·
              refine ⟨9830065129698459961499201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553376753132306640999467 9830065129698459961499201)
              ·
                refine ⟨7372548847273844971124401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9830065129698459961499201 7372548847273844971124401)
                ·
                  refine ⟨5529411635455383728343301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372548847273844971124401 5529411635455383728343301)
                  ·
                    refine ⟨1036764681647884449064369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529411635455383728343301 1036764681647884449064369)
                    ·
                      rfl

theorem cell22_3028638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3028638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028638 prefixEnd_3028638 := by exact prefixLift 3028638
  have htrace : WordTrace (prefixWord ++ tailWord_3028638) baseStart_3028638 baseEnd_3028638 := by
    simpa [prefixWord, tailWord_3028638, baseEnd_3028638] using wordTrace_append hprefix tailTrace_3028638
  have hstable : (prefixWord ++ tailWord_3028638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028638).length < 2 ^ (prefixWord ++ tailWord_3028638).sum := by decide
  have hdescent : baseEnd_3028638 < baseStart_3028638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028642 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3028642 : Nat := 118140960795 + 3028642 * 2 ^ 59
def prefixEnd_3028642 : Nat := 4983230072969 + 3 ^ 40 * 3028642 * 2
def baseEnd_3028642 : Nat := 345588683643209923988119

theorem tailTrace_3028642 : CollatzResearch.WordTrace tailWord_3028642 prefixEnd_3028642 345588683643209923988119 := by
  unfold tailWord_3028642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27615912173438689929566045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73642432462503173145509453 27615912173438689929566045)
  ·
    refine ⟨10355967065039508723587267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27615912173438689929566045 10355967065039508723587267)
    ·
      refine ⟨15533950597559263085380901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10355967065039508723587267 15533950597559263085380901)
      ·
        refine ⟨2912615737042361828508919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15533950597559263085380901 2912615737042361828508919)
        ·
          refine ⟨4368923605563542742763379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2912615737042361828508919 4368923605563542742763379)
          ·
            refine ⟨6553385408345314114145069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368923605563542742763379 6553385408345314114145069)
            ·
              refine ⟨2457519528129492792804401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6553385408345314114145069 2457519528129492792804401)
              ·
                refine ⟨1843139646097119594603301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457519528129492792804401 1843139646097119594603301)
                ·
                  refine ⟨345588683643209923988119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1843139646097119594603301 345588683643209923988119)
                  ·
                    rfl

theorem cell22_3028642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3028642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028642 prefixEnd_3028642 := by exact prefixLift 3028642
  have htrace : WordTrace (prefixWord ++ tailWord_3028642) baseStart_3028642 baseEnd_3028642 := by
    simpa [prefixWord, tailWord_3028642, baseEnd_3028642] using wordTrace_append hprefix tailTrace_3028642
  have hstable : (prefixWord ++ tailWord_3028642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028642).length < 2 ^ (prefixWord ++ tailWord_3028642).sum := by decide
  have hdescent : baseEnd_3028642 < baseStart_3028642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028726 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3028726 : Nat := 118140960795 + 3028726 * 2 ^ 59
def prefixEnd_3028726 : Nat := 4983230072969 + 3 ^ 40 * 3028726 * 2
def baseEnd_3028726 : Nat := 345598268615427184288033

theorem tailTrace_3028726 : CollatzResearch.WordTrace tailWord_3028726 prefixEnd_3028726 345598268615427184288033 := by
  unfold tailWord_3028726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904169526590652629020127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73644474950300294709548021 6904169526590652629020127)
  ·
    refine ⟨10356254289885978943530191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6904169526590652629020127 10356254289885978943530191)
    ·
      refine ⟨15534381434828968415295287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356254289885978943530191 15534381434828968415295287)
      ·
        refine ⟨23301572152243452622942931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15534381434828968415295287 23301572152243452622942931)
        ·
          refine ⟨34952358228365178934414397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23301572152243452622942931 34952358228365178934414397)
          ·
            refine ⟨13107134335636942100405399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34952358228365178934414397 13107134335636942100405399)
            ·
              refine ⟨19660701503455413150608099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13107134335636942100405399 19660701503455413150608099)
              ·
                refine ⟨29491052255183119725912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19660701503455413150608099 29491052255183119725912149)
                ·
                  refine ⟨345598268615427184288033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29491052255183119725912149 345598268615427184288033)
                  ·
                    rfl

theorem cell22_3028726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3028726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028726 prefixEnd_3028726 := by exact prefixLift 3028726
  have htrace : WordTrace (prefixWord ++ tailWord_3028726) baseStart_3028726 baseEnd_3028726 := by
    simpa [prefixWord, tailWord_3028726, baseEnd_3028726] using wordTrace_append hprefix tailTrace_3028726
  have hstable : (prefixWord ++ tailWord_3028726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028726).length < 2 ^ (prefixWord ++ tailWord_3028726).sum := by decide
  have hdescent : baseEnd_3028726 < baseStart_3028726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028788 : List Nat := [2, 5, 1, 1, 2, 2, 1, 8]
def baseStart_3028788 : Nat := 118140960795 + 3028788 * 2 ^ 59
def prefixEnd_3028788 : Nat := 4983230072969 + 3 ^ 40 * 3028788 * 2
def baseEnd_3028788 : Nat := 115201781079259339757101

theorem tailTrace_3028788 : CollatzResearch.WordTrace tailWord_3028788 prefixEnd_3028788 115201781079259339757101 := by
  unfold tailWord_3028788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55234486875612913326539509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73645982500817217768719345 55234486875612913326539509)
  ·
    refine ⟨5178233144588710624363079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55234486875612913326539509 5178233144588710624363079)
    ·
      refine ⟨7767349716883065936544619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178233144588710624363079 7767349716883065936544619)
      ·
        refine ⟨11651024575324598904816929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767349716883065936544619 11651024575324598904816929)
        ·
          refine ⟨8738268431493449178612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11651024575324598904816929 8738268431493449178612697)
          ·
            refine ⟨6553701323620086883959523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8738268431493449178612697 6553701323620086883959523)
            ·
              refine ⟨9830551985430130325939285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553701323620086883959523 9830551985430130325939285)
              ·
                refine ⟨115201781079259339757101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9830551985430130325939285 115201781079259339757101)
                ·
                  rfl

theorem cell22_3028788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_3028788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028788 prefixEnd_3028788 := by exact prefixLift 3028788
  have htrace : WordTrace (prefixWord ++ tailWord_3028788) baseStart_3028788 baseEnd_3028788 := by
    simpa [prefixWord, tailWord_3028788, baseEnd_3028788] using wordTrace_append hprefix tailTrace_3028788
  have hstable : (prefixWord ++ tailWord_3028788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028788).length < 2 ^ (prefixWord ++ tailWord_3028788).sum := by decide
  have hdescent : baseEnd_3028788 < baseStart_3028788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028816 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_3028816 : Nat := 118140960795 + 3028816 * 2 ^ 59
def prefixEnd_3028816 : Nat := 4983230072969 + 3 ^ 40 * 3028816 * 2
def baseEnd_3028816 : Nat := 345608538228517106037941

theorem tailTrace_3028816 : CollatzResearch.WordTrace tailWord_3028816 prefixEnd_3028816 345608538228517106037941 := by
  unfold tailWord_3028816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55234997497562193717549151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73646663330082924956732201 55234997497562193717549151)
  ·
    refine ⟨82852496246343290576323727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55234997497562193717549151 82852496246343290576323727)
    ·
      refine ⟨124278744369514935864485591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82852496246343290576323727 124278744369514935864485591)
      ·
        refine ⟨186418116554272403796728387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124278744369514935864485591 186418116554272403796728387)
        ·
          refine ⟨279627174831408605695092581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186418116554272403796728387 279627174831408605695092581)
          ·
            refine ⟨52430095280889113567829859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279627174831408605695092581 52430095280889113567829859)
            ·
              refine ⟨78645142921333670351744789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52430095280889113567829859 78645142921333670351744789)
              ·
                refine ⟨3686491074437515797738037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78645142921333670351744789 3686491074437515797738037)
                ·
                  refine ⟨345608538228517106037941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3686491074437515797738037 345608538228517106037941)
                  ·
                    rfl

theorem cell22_3028816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_3028816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028816 prefixEnd_3028816 := by exact prefixLift 3028816
  have htrace : WordTrace (prefixWord ++ tailWord_3028816) baseStart_3028816 baseEnd_3028816 := by
    simpa [prefixWord, tailWord_3028816, baseEnd_3028816] using wordTrace_append hprefix tailTrace_3028816
  have hstable : (prefixWord ++ tailWord_3028816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028816).length < 2 ^ (prefixWord ++ tailWord_3028816).sum := by decide
  have hdescent : baseEnd_3028816 < baseStart_3028816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028820 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3028820 : Nat := 118140960795 + 3028820 * 2 ^ 59
def prefixEnd_3028820 : Nat := 4983230072969 + 3 ^ 40 * 3028820 * 2
def baseEnd_3028820 : Nat := 1036826983967296641013811

theorem tailTrace_3028820 : CollatzResearch.WordTrace tailWord_3028820 prefixEnd_3028820 1036826983967296641013811 := by
  unfold tailWord_3028820
  simp only [CollatzResearch.WordTrace]
  refine ⟨55235070443554948059121957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73646760591406597412162609 55235070443554948059121957)
  ·
    refine ⟨10356575708166552761085367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55235070443554948059121957 10356575708166552761085367)
    ·
      refine ⟨15534863562249829141628051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356575708166552761085367 15534863562249829141628051)
      ·
        refine ⟨23302295343374743712442077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15534863562249829141628051 23302295343374743712442077)
        ·
          refine ⟨8738360753765528892165779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23302295343374743712442077 8738360753765528892165779)
          ·
            refine ⟨13107541130648293338248669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738360753765528892165779 13107541130648293338248669)
            ·
              refine ⟨4915327923993110001843251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13107541130648293338248669 4915327923993110001843251)
              ·
                refine ⟨7372991885989665002764877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915327923993110001843251 7372991885989665002764877)
                ·
                  refine ⟨2764871957246124376036829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7372991885989665002764877 2764871957246124376036829)
                  ·
                    refine ⟨1036826983967296641013811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764871957246124376036829 1036826983967296641013811)
                    ·
                      rfl

theorem cell22_3028820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3028820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028820 prefixEnd_3028820 := by exact prefixLift 3028820
  have htrace : WordTrace (prefixWord ++ tailWord_3028820) baseStart_3028820 baseEnd_3028820 := by
    simpa [prefixWord, tailWord_3028820, baseEnd_3028820] using wordTrace_append hprefix tailTrace_3028820
  have hstable : (prefixWord ++ tailWord_3028820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028820).length < 2 ^ (prefixWord ++ tailWord_3028820).sum := by decide
  have hdescent : baseEnd_3028820 < baseStart_3028820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028871 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3028871 : Nat := 118140960795 + 3028871 * 2 ^ 59
def prefixEnd_3028871 : Nat := 4983230072969 + 3 ^ 40 * 3028871 * 2
def baseEnd_3028871 : Nat := 1036844442309549507988655

theorem tailTrace_3028871 : CollatzResearch.WordTrace tailWord_3028871 prefixEnd_3028871 1036844442309549507988655 := by
  unfold tailWord_3028871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110472001009925131828350467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73648000673283421218900311 110472001009925131828350467)
  ·
    refine ⟨165708001514887697742525701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110472001009925131828350467 165708001514887697742525701)
    ·
      refine ⟨31070250284041443326723569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165708001514887697742525701 31070250284041443326723569)
      ·
        refine ⟨23302687713031082495042677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31070250284041443326723569 23302687713031082495042677)
        ·
          refine ⟨2184626973096663983910251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23302687713031082495042677 2184626973096663983910251)
          ·
            refine ⟨3276940459644995975865377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184626973096663983910251 3276940459644995975865377)
            ·
              refine ⟨2457705344733746981899033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276940459644995975865377 2457705344733746981899033)
              ·
                refine ⟨1843279008550310236424275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457705344733746981899033 1843279008550310236424275)
                ·
                  refine ⟨2764918512825465354636413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843279008550310236424275 2764918512825465354636413)
                  ·
                    refine ⟨1036844442309549507988655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764918512825465354636413 1036844442309549507988655)
                    ·
                      rfl

theorem cell22_3028871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3028871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028871 prefixEnd_3028871 := by exact prefixLift 3028871
  have htrace : WordTrace (prefixWord ++ tailWord_3028871) baseStart_3028871 baseEnd_3028871 := by
    simpa [prefixWord, tailWord_3028871, baseEnd_3028871] using wordTrace_append hprefix tailTrace_3028871
  have hstable : (prefixWord ++ tailWord_3028871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028871).length < 2 ^ (prefixWord ++ tailWord_3028871).sum := by decide
  have hdescent : baseEnd_3028871 < baseStart_3028871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028876 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_3028876 : Nat := 118140960795 + 3028876 * 2 ^ 59
def prefixEnd_3028876 : Nat := 4983230072969 + 3 ^ 40 * 3028876 * 2
def baseEnd_3028876 : Nat := 1036846153911731161613639

theorem tailTrace_3028876 : CollatzResearch.WordTrace tailWord_3028876 prefixEnd_3028876 1036846153911731161613639 := by
  unfold tailWord_3028876
  simp only [CollatzResearch.WordTrace]
  refine ⟨55236091687453508841141241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73648122249938011788188321 55236091687453508841141241)
  ·
    refine ⟨41427068765590131630855931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55236091687453508841141241 41427068765590131630855931)
    ·
      refine ⟨62140603148385197446283897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41427068765590131630855931 62140603148385197446283897)
      ·
        refine ⟨46605452361288898084712923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62140603148385197446283897 46605452361288898084712923)
        ·
          refine ⟨69908178541933347127069385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46605452361288898084712923 69908178541933347127069385)
          ·
            refine ⟨52431133906450010345302039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69908178541933347127069385 52431133906450010345302039)
            ·
              refine ⟨78646700859675015517953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52431133906450010345302039 78646700859675015517953059)
              ·
                refine ⟨117970051289512523276929589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78646700859675015517953059 117970051289512523276929589)
                ·
                  refine ⟨11059692308391799057212149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117970051289512523276929589 11059692308391799057212149)
                  ·
                    refine ⟨1036846153911731161613639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11059692308391799057212149 1036846153911731161613639)
                    ·
                      rfl

theorem cell22_3028876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_3028876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028876 prefixEnd_3028876 := by exact prefixLift 3028876
  have htrace : WordTrace (prefixWord ++ tailWord_3028876) baseStart_3028876 baseEnd_3028876 := by
    simpa [prefixWord, tailWord_3028876, baseEnd_3028876] using wordTrace_append hprefix tailTrace_3028876
  have hstable : (prefixWord ++ tailWord_3028876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028876).length < 2 ^ (prefixWord ++ tailWord_3028876).sum := by decide
  have hdescent : baseEnd_3028876 < baseStart_3028876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028893 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3028893 : Nat := 118140960795 + 3028893 * 2 ^ 59
def prefixEnd_3028893 : Nat := 4983230072969 + 3 ^ 40 * 3028893 * 2
def baseEnd_3028893 : Nat := 1036851973359148783938587

theorem tailTrace_3028893 : CollatzResearch.WordTrace tailWord_3028893 prefixEnd_3028893 1036851973359148783938587 := by
  unfold tailWord_3028893
  simp only [CollatzResearch.WordTrace]
  refine ⟨110472803415845429585651333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73648535610563619723767555 110472803415845429585651333)
  ·
    refine ⟨20713650640471018047309625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110472803415845429585651333 20713650640471018047309625)
    ·
      refine ⟨15535237980353263535482219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20713650640471018047309625 15535237980353263535482219)
      ·
        refine ⟨23302856970529895303223329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15535237980353263535482219 23302856970529895303223329)
        ·
          refine ⟨17477142727897421477417497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23302856970529895303223329 17477142727897421477417497)
          ·
            refine ⟨13107857045923066108063123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17477142727897421477417497 13107857045923066108063123)
            ·
              refine ⟨19661785568884599162094685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13107857045923066108063123 19661785568884599162094685)
              ·
                refine ⟨7373169588331724685785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19661785568884599162094685 7373169588331724685785507)
                ·
                  refine ⟨11059754382497587028678261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373169588331724685785507 11059754382497587028678261)
                  ·
                    refine ⟨1036851973359148783938587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11059754382497587028678261 1036851973359148783938587)
                    ·
                      rfl

theorem cell22_3028893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3028893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028893 prefixEnd_3028893 := by exact prefixLift 3028893
  have htrace : WordTrace (prefixWord ++ tailWord_3028893) baseStart_3028893 baseEnd_3028893 := by
    simpa [prefixWord, tailWord_3028893, baseEnd_3028893] using wordTrace_append hprefix tailTrace_3028893
  have hstable : (prefixWord ++ tailWord_3028893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028893).length < 2 ^ (prefixWord ++ tailWord_3028893).sum := by decide
  have hdescent : baseEnd_3028893 < baseStart_3028893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028957 : List Nat := [1, 4, 3, 1, 3, 2, 2, 6]
def baseStart_3028957 : Nat := 118140960795 + 3028957 * 2 ^ 59
def prefixEnd_3028957 : Nat := 4983230072969 + 3 ^ 40 * 3028957 * 2
def baseEnd_3028957 : Nat := 115208209096341550037599

theorem tailTrace_3028957 : CollatzResearch.WordTrace tailWord_3028957 prefixEnd_3028957 115208209096341550037599 := by
  unfold tailWord_3028957
  simp only [CollatzResearch.WordTrace]
  refine ⟨110475137687613568515981125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73650091791742379010654083 110475137687613568515981125)
  ·
    refine ⟨20714088316427544096746461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110475137687613568515981125 20714088316427544096746461)
    ·
      refine ⟨7767783118660329036279923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20714088316427544096746461 7767783118660329036279923)
      ·
        refine ⟨11651674677990493554419885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767783118660329036279923 11651674677990493554419885)
        ·
          refine ⟨4369378004246435082907457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11651674677990493554419885 4369378004246435082907457)
          ·
            refine ⟨3277033503184826312180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369378004246435082907457 3277033503184826312180593)
            ·
              refine ⟨2457775127388619734135445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277033503184826312180593 2457775127388619734135445)
              ·
                refine ⟨115208209096341550037599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2457775127388619734135445 115208209096341550037599)
                ·
                  rfl

theorem cell22_3028957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 6].length) (baseStart_3028957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3028957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3028957 prefixEnd_3028957 := by exact prefixLift 3028957
  have htrace : WordTrace (prefixWord ++ tailWord_3028957) baseStart_3028957 baseEnd_3028957 := by
    simpa [prefixWord, tailWord_3028957, baseEnd_3028957] using wordTrace_append hprefix tailTrace_3028957
  have hstable : (prefixWord ++ tailWord_3028957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028957).length < 2 ^ (prefixWord ++ tailWord_3028957).sum := by decide
  have hdescent : baseEnd_3028957 < baseStart_3028957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029045 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_3029045 : Nat := 118140960795 + 3029045 * 2 ^ 59
def prefixEnd_3029045 : Nat := 4983230072969 + 3 ^ 40 * 3029045 * 2
def baseEnd_3029045 : Nat := 1036904006065471054138121

theorem tailTrace_3029045 : CollatzResearch.WordTrace tailWord_3029045 prefixEnd_3029045 1036904006065471054138121 := by
  unfold tailWord_3029045
  simp only [CollatzResearch.WordTrace]
  refine ⟨110478347311294759545184589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73652231540863173030123059 110478347311294759545184589)
  ·
    refine ⟨41429380241735534829444221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110478347311294759545184589 41429380241735534829444221)
    ·
      refine ⟨15536017590650825561041583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41429380241735534829444221 15536017590650825561041583)
      ·
        refine ⟨23304026385976238341562375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15536017590650825561041583 23304026385976238341562375)
        ·
          refine ⟨34956039578964357512343563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23304026385976238341562375 34956039578964357512343563)
          ·
            refine ⟨52434059368446536268515345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34956039578964357512343563 52434059368446536268515345)
            ·
              refine ⟨39325544526334902201386509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52434059368446536268515345 39325544526334902201386509)
              ·
                refine ⟨14747079197375588325519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39325544526334902201386509 14747079197375588325519941)
                ·
                  refine ⟨2765077349507922811034989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14747079197375588325519941 2765077349507922811034989)
                  ·
                    refine ⟨1036904006065471054138121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765077349507922811034989 1036904006065471054138121)
                    ·
                      rfl

theorem cell22_3029045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_3029045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029045 prefixEnd_3029045 := by exact prefixLift 3029045
  have htrace : WordTrace (prefixWord ++ tailWord_3029045) baseStart_3029045 baseEnd_3029045 := by
    simpa [prefixWord, tailWord_3029045, baseEnd_3029045] using wordTrace_append hprefix tailTrace_3029045
  have hstable : (prefixWord ++ tailWord_3029045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029045).length < 2 ^ (prefixWord ++ tailWord_3029045).sum := by decide
  have hdescent : baseEnd_3029045 < baseStart_3029045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029047 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 4]
def baseStart_3029047 : Nat := 118140960795 + 3029047 * 2 ^ 59
def prefixEnd_3029047 : Nat := 4983230072969 + 3 ^ 40 * 3029047 * 2
def baseEnd_3029047 : Nat := 345634896902114571862705

theorem tailTrace_3029047 : CollatzResearch.WordTrace tailWord_3029047 prefixEnd_3029047 345634896902114571862705 := by
  unfold tailWord_3029047
  simp only [CollatzResearch.WordTrace]
  refine ⟨110478420257287513886757395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73652280171525009257838263 110478420257287513886757395)
  ·
    refine ⟨165717630385931270830136093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110478420257287513886757395 165717630385931270830136093)
    ·
      refine ⟨62144111394724226561301035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165717630385931270830136093 62144111394724226561301035)
      ·
        refine ⟨93216167092086339841951553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62144111394724226561301035 93216167092086339841951553)
        ·
          refine ⟨69912125319064754881463665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93216167092086339841951553 69912125319064754881463665)
          ·
            refine ⟨52434093989298566161097749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69912125319064754881463665 52434093989298566161097749)
            ·
              refine ⟨2457848155748370288801457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52434093989298566161097749 2457848155748370288801457)
              ·
                refine ⟨1843386116811277716601093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457848155748370288801457 1843386116811277716601093)
                ·
                  refine ⟨345634896902114571862705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1843386116811277716601093 345634896902114571862705)
                  ·
                    rfl

theorem cell22_3029047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 4].length) (baseStart_3029047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029047 prefixEnd_3029047 := by exact prefixLift 3029047
  have htrace : WordTrace (prefixWord ++ tailWord_3029047) baseStart_3029047 baseEnd_3029047 := by
    simpa [prefixWord, tailWord_3029047, baseEnd_3029047] using wordTrace_append hprefix tailTrace_3029047
  have hstable : (prefixWord ++ tailWord_3029047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029047).length < 2 ^ (prefixWord ++ tailWord_3029047).sum := by decide
  have hdescent : baseEnd_3029047 < baseStart_3029047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029077 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_3029077 : Nat := 118140960795 + 3029077 * 2 ^ 59
def prefixEnd_3029077 : Nat := 4983230072969 + 3 ^ 40 * 3029077 * 2
def baseEnd_3029077 : Nat := 1036914960319433637338023

theorem tailTrace_3029077 : CollatzResearch.WordTrace tailWord_3029077 prefixEnd_3029077 1036914960319433637338023 := by
  unfold tailWord_3029077
  simp only [CollatzResearch.WordTrace]
  refine ⟨110479514447178829010349485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73653009631452552673566323 110479514447178829010349485)
  ·
    refine ⟨41429817917692060878881057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110479514447178829010349485 41429817917692060878881057)
    ·
      refine ⟨31072363438269045659160793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41429817917692060878881057 31072363438269045659160793)
      ·
        refine ⟨23304272578701784244370595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31072363438269045659160793 23304272578701784244370595)
        ·
          refine ⟨34956408868052676366555893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23304272578701784244370595 34956408868052676366555893)
          ·
            refine ⟨3277163331379938409364615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34956408868052676366555893 3277163331379938409364615)
            ·
              refine ⟨4915744997069907614046923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277163331379938409364615 4915744997069907614046923)
              ·
                refine ⟨7373617495604861421070385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915744997069907614046923 7373617495604861421070385)
                ·
                  refine ⟨5530213121703646065802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7373617495604861421070385 5530213121703646065802789)
                  ·
                    refine ⟨1036914960319433637338023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530213121703646065802789 1036914960319433637338023)
                    ·
                      rfl

theorem cell22_3029077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_3029077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029077 prefixEnd_3029077 := by exact prefixLift 3029077
  have htrace : WordTrace (prefixWord ++ tailWord_3029077) baseStart_3029077 baseEnd_3029077 := by
    simpa [prefixWord, tailWord_3029077, baseEnd_3029077] using wordTrace_append hprefix tailTrace_3029077
  have hstable : (prefixWord ++ tailWord_3029077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029077).length < 2 ^ (prefixWord ++ tailWord_3029077).sum := by decide
  have hdescent : baseEnd_3029077 < baseStart_3029077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029184 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_3029184 : Nat := 118140960795 + 3029184 * 2 ^ 59
def prefixEnd_3029184 : Nat := 4983230072969 + 3 ^ 40 * 3029184 * 2
def baseEnd_3029184 : Nat := 1036951588606121024912695

theorem tailTrace_3029184 : CollatzResearch.WordTrace tailWord_3029184 prefixEnd_3029184 1036951588606121024912695 := by
  unfold tailWord_3029184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55241708528895593142247303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73655611371860790856329737 55241708528895593142247303)
  ·
    refine ⟨82862562793343389713370955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55241708528895593142247303 82862562793343389713370955)
    ·
      refine ⟨124293844190015084570056433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82862562793343389713370955 124293844190015084570056433)
      ·
        refine ⟨93220383142511313427542325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124293844190015084570056433 93220383142511313427542325)
        ·
          refine ⟨8739410919610435633832093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93220383142511313427542325 8739410919610435633832093)
          ·
            refine ⟨3277279094853913362687035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8739410919610435633832093 3277279094853913362687035)
            ·
              refine ⟨4915918642280870044030553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277279094853913362687035 4915918642280870044030553)
              ·
                refine ⟨3686938981710652533022915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915918642280870044030553 3686938981710652533022915)
                ·
                  refine ⟨5530408472565978799534373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686938981710652533022915 5530408472565978799534373)
                  ·
                    refine ⟨1036951588606121024912695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530408472565978799534373 1036951588606121024912695)
                    ·
                      rfl

theorem cell22_3029184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_3029184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029184 prefixEnd_3029184 := by exact prefixLift 3029184
  have htrace : WordTrace (prefixWord ++ tailWord_3029184) baseStart_3029184 baseEnd_3029184 := by
    simpa [prefixWord, tailWord_3029184, baseEnd_3029184] using wordTrace_append hprefix tailTrace_3029184
  have hstable : (prefixWord ++ tailWord_3029184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029184).length < 2 ^ (prefixWord ++ tailWord_3029184).sum := by decide
  have hdescent : baseEnd_3029184 < baseStart_3029184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029242 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_3029242 : Nat := 118140960795 + 3029242 * 2 ^ 59
def prefixEnd_3029242 : Nat := 4983230072969 + 3 ^ 40 * 3029242 * 2
def baseEnd_3029242 : Nat := 1036971443191428206962517

theorem tailTrace_3029242 : CollatzResearch.WordTrace tailWord_3029242 prefixEnd_3029242 1036971443191428206962517 := by
  unfold tailWord_3029242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27621383122895265547526495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73657021661054041460070653 27621383122895265547526495)
  ·
    refine ⟨41432074684342898321289743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27621383122895265547526495 41432074684342898321289743)
    ·
      refine ⟨62148112026514347481934615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41432074684342898321289743 62148112026514347481934615)
      ·
        refine ⟨93222168039771521222901923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62148112026514347481934615 93222168039771521222901923)
        ·
          refine ⟨139833252059657281834352885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93222168039771521222901923 139833252059657281834352885)
          ·
            refine ⟨13109367380592870171970583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139833252059657281834352885 13109367380592870171970583)
            ·
              refine ⟨19664051070889305257955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109367380592870171970583 19664051070889305257955875)
              ·
                refine ⟨29496076606333957886933813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19664051070889305257955875 29496076606333957886933813)
                ·
                  refine ⟨2765257181843808551900045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29496076606333957886933813 2765257181843808551900045)
                  ·
                    refine ⟨1036971443191428206962517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765257181843808551900045 1036971443191428206962517)
                    ·
                      rfl

theorem cell22_3029242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_3029242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029242 prefixEnd_3029242 := by exact prefixLift 3029242
  have htrace : WordTrace (prefixWord ++ tailWord_3029242) baseStart_3029242 baseEnd_3029242 := by
    simpa [prefixWord, tailWord_3029242, baseEnd_3029242] using wordTrace_append hprefix tailTrace_3029242
  have hstable : (prefixWord ++ tailWord_3029242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029242).length < 2 ^ (prefixWord ++ tailWord_3029242).sum := by decide
  have hdescent : baseEnd_3029242 < baseStart_3029242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029340 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_3029340 : Nat := 118140960795 + 3029340 * 2 ^ 59
def prefixEnd_3029340 : Nat := 4983230072969 + 3 ^ 40 * 3029340 * 2
def baseEnd_3029340 : Nat := 345668330198062872670739

theorem tailTrace_3029340 : CollatzResearch.WordTrace tailWord_3029340 prefixEnd_3029340 345668330198062872670739 := by
  unfold tailWord_3029340
  simp only [CollatzResearch.WordTrace]
  refine ⟨55244553422613012463586737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73659404563484016618115649 55244553422613012463586737)
  ·
    refine ⟨41433415066959759347690053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55244553422613012463586737 41433415066959759347690053)
    ·
      refine ⟨7768765325054954877691885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41433415066959759347690053 7768765325054954877691885)
      ·
        refine ⟨2913286996895608079134457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7768765325054954877691885 2913286996895608079134457)
        ·
          refine ⟨2184965247671706059350843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2913286996895608079134457 2184965247671706059350843)
          ·
            refine ⟨3277447871507559089026265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184965247671706059350843 3277447871507559089026265)
            ·
              refine ⟨2458085903630669316769699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277447871507559089026265 2458085903630669316769699)
              ·
                refine ⟨3687128855446003975154549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458085903630669316769699 3687128855446003975154549)
                ·
                  refine ⟨345668330198062872670739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3687128855446003975154549 345668330198062872670739)
                  ·
                    rfl

theorem cell22_3029340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_3029340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029340 prefixEnd_3029340 := by exact prefixLift 3029340
  have htrace : WordTrace (prefixWord ++ tailWord_3029340) baseStart_3029340 baseEnd_3029340 := by
    simpa [prefixWord, tailWord_3029340, baseEnd_3029340] using wordTrace_append hprefix tailTrace_3029340
  have hstable : (prefixWord ++ tailWord_3029340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029340).length < 2 ^ (prefixWord ++ tailWord_3029340).sum := by decide
  have hdescent : baseEnd_3029340 < baseStart_3029340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029347 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_3029347 : Nat := 118140960795 + 3029347 * 2 ^ 59
def prefixEnd_3029347 : Nat := 4983230072969 + 3 ^ 40 * 3029347 * 2
def baseEnd_3029347 : Nat := 1037007386837242933087195

theorem tailTrace_3029347 : CollatzResearch.WordTrace tailWord_3029347 prefixEnd_3029347 1037007386837242933087195 := by
  unfold tailWord_3029347
  simp only [CollatzResearch.WordTrace]
  refine ⟨110489362156200665122678295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73659574770800443415118863 110489362156200665122678295)
  ·
    refine ⟨165734043234300997684017443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110489362156200665122678295 165734043234300997684017443)
    ·
      refine ⟨248601064851451496526026165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165734043234300997684017443 248601064851451496526026165)
      ·
        refine ⟨23306349829823577799314953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248601064851451496526026165 23306349829823577799314953)
        ·
          refine ⟨17479762372367683349486215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23306349829823577799314953 17479762372367683349486215)
          ·
            refine ⟨26219643558551525024229323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17479762372367683349486215 26219643558551525024229323)
            ·
              refine ⟨39329465337827287536343985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26219643558551525024229323 39329465337827287536343985)
              ·
                refine ⟨29497099003370465652257989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39329465337827287536343985 29497099003370465652257989)
                ·
                  refine ⟨5530706063131962309798373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29497099003370465652257989 5530706063131962309798373)
                  ·
                    refine ⟨1037007386837242933087195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530706063131962309798373 1037007386837242933087195)
                    ·
                      rfl

theorem cell22_3029347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_3029347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029347 prefixEnd_3029347 := by exact prefixLift 3029347
  have htrace : WordTrace (prefixWord ++ tailWord_3029347) baseStart_3029347 baseEnd_3029347 := by
    simpa [prefixWord, tailWord_3029347, baseEnd_3029347] using wordTrace_append hprefix tailTrace_3029347
  have hstable : (prefixWord ++ tailWord_3029347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029347).length < 2 ^ (prefixWord ++ tailWord_3029347).sum := by decide
  have hdescent : baseEnd_3029347 < baseStart_3029347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029362 : List Nat := [3, 2, 1, 2, 1, 3, 2, 8]
def baseStart_3029362 : Nat := 118140960795 + 3029362 * 2 ^ 59
def prefixEnd_3029362 : Nat := 4983230072969 + 3 ^ 40 * 3029362 * 2
def baseEnd_3029362 : Nat := 115223613515976432662461

theorem tailTrace_3029362 : CollatzResearch.WordTrace tailWord_3029362 prefixEnd_3029362 115223613515976432662461 := by
  unfold tailWord_3029362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27622477312786580671118585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73659939500764215122982893 27622477312786580671118585)
  ·
    refine ⟨20716857984589935503338939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27622477312786580671118585 20716857984589935503338939)
    ·
      refine ⟨31075286976884903255008409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20716857984589935503338939 31075286976884903255008409)
      ·
        refine ⟨23306465232663677441256307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31075286976884903255008409 23306465232663677441256307)
        ·
          refine ⟨34959697848995516161884461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23306465232663677441256307 34959697848995516161884461)
          ·
            refine ⟨13109886693373318560706673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34959697848995516161884461 13109886693373318560706673)
            ·
              refine ⟨9832415020029988920530005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13109886693373318560706673 9832415020029988920530005)
              ·
                refine ⟨115223613515976432662461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9832415020029988920530005 115223613515976432662461)
                ·
                  rfl

theorem cell22_3029362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_3029362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029362 prefixEnd_3029362 := by exact prefixLift 3029362
  have htrace : WordTrace (prefixWord ++ tailWord_3029362) baseStart_3029362 baseEnd_3029362 := by
    simpa [prefixWord, tailWord_3029362, baseEnd_3029362] using wordTrace_append hprefix tailTrace_3029362
  have hstable : (prefixWord ++ tailWord_3029362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029362).length < 2 ^ (prefixWord ++ tailWord_3029362).sum := by decide
  have hdescent : baseEnd_3029362 < baseStart_3029362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029396 : List Nat := [2, 4, 2, 1, 3, 2, 1, 7]
def baseStart_3029396 : Nat := 118140960795 + 3029396 * 2 ^ 59
def prefixEnd_3029396 : Nat := 4983230072969 + 3 ^ 40 * 3029396 * 2
def baseEnd_3029396 : Nat := 115224906726513682068005

theorem tailTrace_3029396 : CollatzResearch.WordTrace tailWord_3029396 prefixEnd_3029396 115224906726513682068005 := by
  unfold tailWord_3029396
  simp only [CollatzResearch.WordTrace]
  refine ⟨55245574666511573245606021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73660766222015430994141361 55245574666511573245606021)
  ·
    refine ⟨10358545249970919983551129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55245574666511573245606021 10358545249970919983551129)
    ·
      refine ⟨7768908937478189987663347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10358545249970919983551129 7768908937478189987663347)
      ·
        refine ⟨11653363406217284981495021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7768908937478189987663347 11653363406217284981495021)
        ·
          refine ⟨4370011277331481868060633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11653363406217284981495021 4370011277331481868060633)
          ·
            refine ⟨3277508457998611401045475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4370011277331481868060633 3277508457998611401045475)
            ·
              refine ⟨4916262686997917101568213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277508457998611401045475 4916262686997917101568213)
              ·
                refine ⟨115224906726513682068005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4916262686997917101568213 115224906726513682068005)
                ·
                  rfl

theorem cell22_3029396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_3029396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029396 prefixEnd_3029396 := by exact prefixLift 3029396
  have htrace : WordTrace (prefixWord ++ tailWord_3029396) baseStart_3029396 baseEnd_3029396 := by
    simpa [prefixWord, tailWord_3029396, baseEnd_3029396] using wordTrace_append hprefix tailTrace_3029396
  have hstable : (prefixWord ++ tailWord_3029396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029396).length < 2 ^ (prefixWord ++ tailWord_3029396).sum := by decide
  have hdescent : baseEnd_3029396 < baseStart_3029396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029469 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3029469 : Nat := 118140960795 + 3029469 * 2 ^ 59
def prefixEnd_3029469 : Nat := 4983230072969 + 3 ^ 40 * 3029469 * 2
def baseEnd_3029469 : Nat := 345683049976825093845607

theorem tailTrace_3029469 : CollatzResearch.WordTrace tailWord_3029469 prefixEnd_3029469 345683049976825093845607 := by
  unfold tailWord_3029469
  simp only [CollatzResearch.WordTrace]
  refine ⟨110493811861758679958619461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73662541241172453305746307 110493811861758679958619461)
  ·
    refine ⟨20717589724079752492241149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110493811861758679958619461 20717589724079752492241149)
    ·
      refine ⟨7769096146529907184590431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20717589724079752492241149 7769096146529907184590431)
      ·
        refine ⟨11653644219794860776885647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769096146529907184590431 11653644219794860776885647)
        ·
          refine ⟨17480466329692291165328471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11653644219794860776885647 17480466329692291165328471)
          ·
            refine ⟨26220699494538436747992707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17480466329692291165328471 26220699494538436747992707)
            ·
              refine ⟨39331049241807655121989061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26220699494538436747992707 39331049241807655121989061)
              ·
                refine ⟨7374571732838935335372949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39331049241807655121989061 7374571732838935335372949)
                ·
                  refine ⟨345683049976825093845607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7374571732838935335372949 345683049976825093845607)
                  ·
                    rfl

theorem cell22_3029469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3029469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029469 prefixEnd_3029469 := by exact prefixLift 3029469
  have htrace : WordTrace (prefixWord ++ tailWord_3029469) baseStart_3029469 baseEnd_3029469 := by
    simpa [prefixWord, tailWord_3029469, baseEnd_3029469] using wordTrace_append hprefix tailTrace_3029469
  have hstable : (prefixWord ++ tailWord_3029469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029469).length < 2 ^ (prefixWord ++ tailWord_3029469).sum := by decide
  have hdescent : baseEnd_3029469 < baseStart_3029469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029471 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 1, 4]
def baseStart_3029471 : Nat := 118140960795 + 3029471 * 2 ^ 59
def prefixEnd_3029471 : Nat := 4983230072969 + 3 ^ 40 * 3029471 * 2
def baseEnd_3029471 : Nat := 1037049834571347942986815

theorem tailTrace_3029471 : CollatzResearch.WordTrace tailWord_3029471 prefixEnd_3029471 1037049834571347942986815 := by
  unfold tailWord_3029471
  simp only [CollatzResearch.WordTrace]
  refine ⟨110493884807751434300192267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73662589871834289533461511 110493884807751434300192267)
  ·
    refine ⟨165740827211627151450288401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110493884807751434300192267 165740827211627151450288401)
    ·
      refine ⟨124305620408720363587716301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165740827211627151450288401 124305620408720363587716301)
      ·
        refine ⟨46614607653270136345393613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124305620408720363587716301 46614607653270136345393613)
        ·
          refine ⟨17480477869976301129522605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46614607653270136345393613 17480477869976301129522605)
          ·
            refine ⟨6555179201241112923570977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17480477869976301129522605 6555179201241112923570977)
            ·
              refine ⟨4916384400930834692678233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6555179201241112923570977 4916384400930834692678233)
              ·
                refine ⟨3687288300698126019508675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916384400930834692678233 3687288300698126019508675)
                ·
                  refine ⟨5530932451047189029263013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687288300698126019508675 5530932451047189029263013)
                  ·
                    refine ⟨1037049834571347942986815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530932451047189029263013 1037049834571347942986815)
                    ·
                      rfl

theorem cell22_3029471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_3029471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029471 prefixEnd_3029471 := by exact prefixLift 3029471
  have htrace : WordTrace (prefixWord ++ tailWord_3029471) baseStart_3029471 baseEnd_3029471 := by
    simpa [prefixWord, tailWord_3029471, baseEnd_3029471] using wordTrace_append hprefix tailTrace_3029471
  have hstable : (prefixWord ++ tailWord_3029471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029471).length < 2 ^ (prefixWord ++ tailWord_3029471).sum := by decide
  have hdescent : baseEnd_3029471 < baseStart_3029471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029484 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_3029484 : Nat := 118140960795 + 3029484 * 2 ^ 59
def prefixEnd_3029484 : Nat := 4983230072969 + 3 ^ 40 * 3029484 * 2
def baseEnd_3029484 : Nat := 1037054284737020242411775

theorem tailTrace_3029484 : CollatzResearch.WordTrace tailWord_3029484 prefixEnd_3029484 1037054284737020242411775 := by
  unfold tailWord_3029484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55247179478352168760207753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73662905971136225013610337 55247179478352168760207753)
  ·
    refine ⟨41435384608764126570155815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55247179478352168760207753 41435384608764126570155815)
    ·
      refine ⟨62153076913146189855233723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41435384608764126570155815 62153076913146189855233723)
      ·
        refine ⟨93229615369719284782850585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62153076913146189855233723 93229615369719284782850585)
        ·
          refine ⟨69922211527289463587137939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93229615369719284782850585 69922211527289463587137939)
          ·
            refine ⟨104883317290934195380706909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69922211527289463587137939 104883317290934195380706909)
            ·
              refine ⟨39331243984100323267765091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104883317290934195380706909 39331243984100323267765091)
              ·
                refine ⟨58996865976150484901647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39331243984100323267765091 58996865976150484901647637)
                ·
                  refine ⟨2765478092632053979764733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58996865976150484901647637 2765478092632053979764733)
                  ·
                    refine ⟨1037054284737020242411775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765478092632053979764733 1037054284737020242411775)
                    ·
                      rfl

theorem cell22_3029484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_3029484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029484 prefixEnd_3029484 := by exact prefixLift 3029484
  have htrace : WordTrace (prefixWord ++ tailWord_3029484) baseStart_3029484 baseEnd_3029484 := by
    simpa [prefixWord, tailWord_3029484, baseEnd_3029484] using wordTrace_append hprefix tailTrace_3029484
  have hstable : (prefixWord ++ tailWord_3029484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029484).length < 2 ^ (prefixWord ++ tailWord_3029484).sum := by decide
  have hdescent : baseEnd_3029484 < baseStart_3029484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029497 : List Nat := [1, 2, 1, 3, 1, 2, 12]
def baseStart_3029497 : Nat := 118140960795 + 3029497 * 2 ^ 59
def prefixEnd_3029497 : Nat := 4983230072969 + 3 ^ 40 * 3029497 * 2
def baseEnd_3029497 : Nat := 38409582774173797845805

theorem tailTrace_3029497 : CollatzResearch.WordTrace tailWord_3029497 prefixEnd_3029497 38409582774173797845805 := by
  unfold tailWord_3029497
  simp only [CollatzResearch.WordTrace]
  refine ⟨110494833105657240740638745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73663222070438160493759163 110494833105657240740638745)
  ·
    refine ⟨82871124829242930555479059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110494833105657240740638745 82871124829242930555479059)
    ·
      refine ⟨124306687243864395833218589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82871124829242930555479059 124306687243864395833218589)
      ·
        refine ⟨46615007716449148437456971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124306687243864395833218589 46615007716449148437456971)
        ·
          refine ⟨69922511574673722656185457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46615007716449148437456971 69922511574673722656185457)
          ·
            refine ⟨52441883681005291992139093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69922511574673722656185457 52441883681005291992139093)
            ·
              refine ⟨38409582774173797845805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52441883681005291992139093 38409582774173797845805)
              ·
                rfl

theorem cell22_3029497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 12].length) (baseStart_3029497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029497 prefixEnd_3029497 := by exact prefixLift 3029497
  have htrace : WordTrace (prefixWord ++ tailWord_3029497) baseStart_3029497 baseEnd_3029497 := by
    simpa [prefixWord, tailWord_3029497, baseEnd_3029497] using wordTrace_append hprefix tailTrace_3029497
  have hstable : (prefixWord ++ tailWord_3029497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029497).length < 2 ^ (prefixWord ++ tailWord_3029497).sum := by decide
  have hdescent : baseEnd_3029497 < baseStart_3029497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029501 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_3029501 : Nat := 118140960795 + 3029501 * 2 ^ 59
def prefixEnd_3029501 : Nat := 4983230072969 + 3 ^ 40 * 3029501 * 2
def baseEnd_3029501 : Nat := 1037060104184437864736723

theorem tailTrace_3029501 : CollatzResearch.WordTrace tailWord_3029501 prefixEnd_3029501 1037060104184437864736723 := by
  unfold tailWord_3029501
  simp only [CollatzResearch.WordTrace]
  refine ⟨110494978997642749423784357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73663319331761832949189571 110494978997642749423784357)
  ·
    refine ⟨20717808562058015516959567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110494978997642749423784357 20717808562058015516959567)
    ·
      refine ⟨31076712843087023275439351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717808562058015516959567 31076712843087023275439351)
      ·
        refine ⟨46615069264630534913159027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31076712843087023275439351 46615069264630534913159027)
        ·
          refine ⟨69922603896945802369738541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46615069264630534913159027 69922603896945802369738541)
          ·
            refine ⟨26220976461354675888651953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69922603896945802369738541 26220976461354675888651953)
            ·
              refine ⟨19665732346016006916488965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26220976461354675888651953 19665732346016006916488965)
              ·
                refine ⟨3687324814878001296841681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19665732346016006916488965 3687324814878001296841681)
                ·
                  refine ⟨2765493611158500972631261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687324814878001296841681 2765493611158500972631261)
                  ·
                    refine ⟨1037060104184437864736723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765493611158500972631261 1037060104184437864736723)
                    ·
                      rfl

theorem cell22_3029501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_3029501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029501 prefixEnd_3029501 := by exact prefixLift 3029501
  have htrace : WordTrace (prefixWord ++ tailWord_3029501) baseStart_3029501 baseEnd_3029501 := by
    simpa [prefixWord, tailWord_3029501, baseEnd_3029501] using wordTrace_append hprefix tailTrace_3029501
  have hstable : (prefixWord ++ tailWord_3029501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029501).length < 2 ^ (prefixWord ++ tailWord_3029501).sum := by decide
  have hdescent : baseEnd_3029501 < baseStart_3029501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029514 : List Nat := [3, 1, 2, 2, 2, 1, 4, 7]
def baseStart_3029514 : Nat := 118140960795 + 3029514 * 2 ^ 59
def prefixEnd_3029514 : Nat := 4983230072969 + 3 ^ 40 * 3029514 * 2
def baseEnd_3029514 : Nat := 115229394927790018240187

theorem tailTrace_3029514 : CollatzResearch.WordTrace tailWord_3029514 prefixEnd_3029514 115229394927790018240187 := by
  unfold tailWord_3029514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623863286648913161001899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73663635431063768429338397 27623863286648913161001899)
  ·
    refine ⟨41435794929973369741502849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623863286648913161001899 41435794929973369741502849)
    ·
      refine ⟨31076846197480027306127137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41435794929973369741502849 31076846197480027306127137)
      ·
        refine ⟨23307634648110020479595353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31076846197480027306127137 23307634648110020479595353)
        ·
          refine ⟨17480725986082515359696515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23307634648110020479595353 17480725986082515359696515)
          ·
            refine ⟨26221088979123773039544773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17480725986082515359696515 26221088979123773039544773)
            ·
              refine ⟨4916454183585707444914645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26221088979123773039544773 4916454183585707444914645)
              ·
                refine ⟨115229394927790018240187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4916454183585707444914645 115229394927790018240187)
                ·
                  rfl

theorem cell22_3029514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_3029514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029514 prefixEnd_3029514 := by exact prefixLift 3029514
  have htrace : WordTrace (prefixWord ++ tailWord_3029514) baseStart_3029514 baseEnd_3029514 := by
    simpa [prefixWord, tailWord_3029514, baseEnd_3029514] using wordTrace_append hprefix tailTrace_3029514
  have hstable : (prefixWord ++ tailWord_3029514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029514).length < 2 ^ (prefixWord ++ tailWord_3029514).sum := by decide
  have hdescent : baseEnd_3029514 < baseStart_3029514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029518 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3029518 : Nat := 118140960795 + 3029518 * 2 ^ 59
def prefixEnd_3029518 : Nat := 4983230072969 + 3 ^ 40 * 3029518 * 2
def baseEnd_3029518 : Nat := 1037065923631855487061671

theorem tailTrace_3029518 : CollatzResearch.WordTrace tailWord_3029518 prefixEnd_3029518 1037065923631855487061671 := by
  unfold tailWord_3029518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811949879822645165894151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73663732692387440884768805 13811949879822645165894151)
  ·
    refine ⟨20717924819733967748841227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811949879822645165894151 20717924819733967748841227)
    ·
      refine ⟨31076887229600951623261841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717924819733967748841227 31076887229600951623261841)
      ·
        refine ⟨23307665422200713717446381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31076887229600951623261841 23307665422200713717446381)
        ·
          refine ⟨8740374533325267644042393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23307665422200713717446381 8740374533325267644042393)
          ·
            refine ⟨6555280899993950733031795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8740374533325267644042393 6555280899993950733031795)
            ·
              refine ⟨9832921349990926099547693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555280899993950733031795 9832921349990926099547693)
              ·
                refine ⟨3687345506246597287330385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9832921349990926099547693 3687345506246597287330385)
                ·
                  refine ⟨2765509129684947965497789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687345506246597287330385 2765509129684947965497789)
                  ·
                    refine ⟨1037065923631855487061671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765509129684947965497789 1037065923631855487061671)
                    ·
                      rfl

theorem cell22_3029518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3029518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029518 prefixEnd_3029518 := by exact prefixLift 3029518
  have htrace : WordTrace (prefixWord ++ tailWord_3029518) baseStart_3029518 baseEnd_3029518 := by
    simpa [prefixWord, tailWord_3029518, baseEnd_3029518] using wordTrace_append hprefix tailTrace_3029518
  have hstable : (prefixWord ++ tailWord_3029518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029518).length < 2 ^ (prefixWord ++ tailWord_3029518).sum := by decide
  have hdescent : baseEnd_3029518 < baseStart_3029518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029604 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3029604 : Nat := 118140960795 + 3029604 * 2 ^ 59
def prefixEnd_3029604 : Nat := 4983230072969 + 3 ^ 40 * 3029604 * 2
def baseEnd_3029604 : Nat := 345698454396459976470469

theorem tailTrace_3029604 : CollatzResearch.WordTrace tailWord_3029604 prefixEnd_3029604 345698454396459976470469 := by
  unfold tailWord_3029604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55249367858134799007391933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73665823810846398676522577 55249367858134799007391933)
  ·
    refine ⟨20718512946800549627771975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55249367858134799007391933 20718512946800549627771975)
    ·
      refine ⟨31077769420200824441657963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20718512946800549627771975 31077769420200824441657963)
      ·
        refine ⟨46616654130301236662486945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31077769420200824441657963 46616654130301236662486945)
        ·
          refine ⟨34962490597725927496865209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46616654130301236662486945 34962490597725927496865209)
          ·
            refine ⟨26221867948294445622648907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34962490597725927496865209 26221867948294445622648907)
            ·
              refine ⟨39332801922441668433973361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26221867948294445622648907 39332801922441668433973361)
              ·
                refine ⟨29499601441831251325480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39332801922441668433973361 29499601441831251325480021)
                ·
                  refine ⟨345698454396459976470469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29499601441831251325480021 345698454396459976470469)
                  ·
                    rfl

theorem cell22_3029604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3029604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029604 prefixEnd_3029604 := by exact prefixLift 3029604
  have htrace : WordTrace (prefixWord ++ tailWord_3029604) baseStart_3029604 baseEnd_3029604 := by
    simpa [prefixWord, tailWord_3029604, baseEnd_3029604] using wordTrace_append hprefix tailTrace_3029604
  have hstable : (prefixWord ++ tailWord_3029604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029604).length < 2 ^ (prefixWord ++ tailWord_3029604).sum := by decide
  have hdescent : baseEnd_3029604 < baseStart_3029604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029687 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 2, 3]
def baseStart_3029687 : Nat := 118140960795 + 3029687 * 2 ^ 59
def prefixEnd_3029687 : Nat := 4983230072969 + 3 ^ 40 * 3029687 * 2
def baseEnd_3029687 : Nat := 1037123775785595379586153

theorem tailTrace_3029687 : CollatzResearch.WordTrace tailWord_3029687 prefixEnd_3029687 1037123775785595379586153 := by
  unfold tailWord_3029687
  simp only [CollatzResearch.WordTrace]
  refine ⟨110501762974968903190055315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73667841983312602126703543 110501762974968903190055315)
  ·
    refine ⟨165752644462453354785082973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110501762974968903190055315 165752644462453354785082973)
    ·
      refine ⟨62157241673420008044406115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165752644462453354785082973 62157241673420008044406115)
      ·
        refine ⟨93235862510130012066609173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62157241673420008044406115 93235862510130012066609173)
        ·
          refine ⟨4370431055162344315622305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93235862510130012066609173 4370431055162344315622305)
          ·
            refine ⟨3277823291371758236716729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4370431055162344315622305 3277823291371758236716729)
            ·
              refine ⟨2458367468528818677537547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277823291371758236716729 2458367468528818677537547)
              ·
                refine ⟨3687551202793228016306321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458367468528818677537547 3687551202793228016306321)
                ·
                  refine ⟨2765663402094921012229741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687551202793228016306321 2765663402094921012229741)
                  ·
                    refine ⟨1037123775785595379586153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765663402094921012229741 1037123775785595379586153)
                    ·
                      rfl

theorem cell22_3029687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_3029687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029687 prefixEnd_3029687 := by exact prefixLift 3029687
  have htrace : WordTrace (prefixWord ++ tailWord_3029687) baseStart_3029687 baseEnd_3029687 := by
    simpa [prefixWord, tailWord_3029687, baseEnd_3029687] using wordTrace_append hprefix tailTrace_3029687
  have hstable : (prefixWord ++ tailWord_3029687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029687).length < 2 ^ (prefixWord ++ tailWord_3029687).sum := by decide
  have hdescent : baseEnd_3029687 < baseStart_3029687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029732 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_3029732 : Nat := 118140960795 + 3029732 * 2 ^ 59
def prefixEnd_3029732 : Nat := 4983230072969 + 3 ^ 40 * 3029732 * 2
def baseEnd_3029732 : Nat := 1037139180205230262211015

theorem tailTrace_3029732 : CollatzResearch.WordTrace tailWord_3029732 prefixEnd_3029732 1037139180205230262211015 := by
  unfold tailWord_3029732
  simp only [CollatzResearch.WordTrace]
  refine ⟨55251702129902937937721725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73668936173203917250295633 55251702129902937937721725)
  ·
    refine ⟨20719388298713601726645647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55251702129902937937721725 20719388298713601726645647)
    ·
      refine ⟨31079082448070402589968471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20719388298713601726645647 31079082448070402589968471)
      ·
        refine ⟨46618623672105603884952707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079082448070402589968471 46618623672105603884952707)
        ·
          refine ⟨69927935508158405827429061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46618623672105603884952707 69927935508158405827429061)
          ·
            refine ⟨13111487907779701092642949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69927935508158405827429061 13111487907779701092642949)
            ·
              refine ⟨2458403982708693954870553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13111487907779701092642949 2458403982708693954870553)
              ·
                refine ⟨1843802987031520466152915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458403982708693954870553 1843802987031520466152915)
                ·
                  refine ⟨2765704480547280699229373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843802987031520466152915 2765704480547280699229373)
                  ·
                    refine ⟨1037139180205230262211015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765704480547280699229373 1037139180205230262211015)
                    ·
                      rfl

theorem cell22_3029732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_3029732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029732 prefixEnd_3029732 := by exact prefixLift 3029732
  have htrace : WordTrace (prefixWord ++ tailWord_3029732) baseStart_3029732 baseEnd_3029732 := by
    simpa [prefixWord, tailWord_3029732, baseEnd_3029732] using wordTrace_append hprefix tailTrace_3029732
  have hstable : (prefixWord ++ tailWord_3029732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029732).length < 2 ^ (prefixWord ++ tailWord_3029732).sum := by decide
  have hdescent : baseEnd_3029732 < baseStart_3029732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029749 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3029749 : Nat := 118140960795 + 3029749 * 2 ^ 59
def prefixEnd_3029749 : Nat := 4983230072969 + 3 ^ 40 * 3029749 * 2
def baseEnd_3029749 : Nat := 1037144999652647884535963

theorem tailTrace_3029749 : CollatzResearch.WordTrace tailWord_3029749 prefixEnd_3029749 1037144999652647884535963 := by
  unfold tailWord_3029749
  simp only [CollatzResearch.WordTrace]
  refine ⟨110504024300744287778812301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73669349533829525185874867 110504024300744287778812301)
  ·
    refine ⟨41439009112779107917054613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110504024300744287778812301 41439009112779107917054613)
    ·
      refine ⟨1942453552161520683611935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41439009112779107917054613 1942453552161520683611935)
      ·
        refine ⟨2913680328242281025417903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942453552161520683611935 2913680328242281025417903)
        ·
          refine ⟨4370520492363421538126855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913680328242281025417903 4370520492363421538126855)
          ·
            refine ⟨6555780738545132307190283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370520492363421538126855 6555780738545132307190283)
            ·
              refine ⟨9833671107817698460785425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555780738545132307190283 9833671107817698460785425)
              ·
                refine ⟨7375253330863273845589069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9833671107817698460785425 7375253330863273845589069)
                ·
                  refine ⟨2765719999073727692095901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7375253330863273845589069 2765719999073727692095901)
                  ·
                    refine ⟨1037144999652647884535963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765719999073727692095901 1037144999652647884535963)
                    ·
                      rfl

theorem cell22_3029749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3029749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029749 prefixEnd_3029749 := by exact prefixLift 3029749
  have htrace : WordTrace (prefixWord ++ tailWord_3029749) baseStart_3029749 baseEnd_3029749 := by
    simpa [prefixWord, tailWord_3029749, baseEnd_3029749] using wordTrace_append hprefix tailTrace_3029749
  have hstable : (prefixWord ++ tailWord_3029749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029749).length < 2 ^ (prefixWord ++ tailWord_3029749).sum := by decide
  have hdescent : baseEnd_3029749 < baseStart_3029749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029756 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_3029756 : Nat := 118140960795 + 3029756 * 2 ^ 59
def prefixEnd_3029756 : Nat := 4983230072969 + 3 ^ 40 * 3029756 * 2
def baseEnd_3029756 : Nat := 345715798631900733203647

theorem tailTrace_3029756 : CollatzResearch.WordTrace tailWord_3029756 prefixEnd_3029756 345715798631900733203647 := by
  unfold tailWord_3029756
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252139805859463987158561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73669519741145951982878081 55252139805859463987158561)
  ·
    refine ⟨41439104854394597990368921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55252139805859463987158561 41439104854394597990368921)
    ·
      refine ⟨31079328640795948492776691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41439104854394597990368921 31079328640795948492776691)
      ·
        refine ⟨46618992961193922739165037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079328640795948492776691 46618992961193922739165037)
        ·
          refine ⟨17482122360447721027186889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46618992961193922739165037 17482122360447721027186889)
          ·
            refine ⟨13111591770335790770390167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17482122360447721027186889 13111591770335790770390167)
            ·
              refine ⟨19667387655503686155585251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13111591770335790770390167 19667387655503686155585251)
              ·
                refine ⟨29501081483255529233377877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19667387655503686155585251 29501081483255529233377877)
                ·
                  refine ⟨345715798631900733203647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29501081483255529233377877 345715798631900733203647)
                  ·
                    rfl

theorem cell22_3029756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_3029756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029756 prefixEnd_3029756 := by exact prefixLift 3029756
  have htrace : WordTrace (prefixWord ++ tailWord_3029756) baseStart_3029756 baseEnd_3029756 := by
    simpa [prefixWord, tailWord_3029756, baseEnd_3029756] using wordTrace_append hprefix tailTrace_3029756
  have hstable : (prefixWord ++ tailWord_3029756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029756).length < 2 ^ (prefixWord ++ tailWord_3029756).sum := by decide
  have hdescent : baseEnd_3029756 < baseStart_3029756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029816 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3029816 : Nat := 118140960795 + 3029816 * 2 ^ 59
def prefixEnd_3029816 : Nat := 4983230072969 + 3 ^ 40 * 3029816 * 2
def baseEnd_3029816 : Nat := 1037167935121882043110757

theorem tailTrace_3029816 : CollatzResearch.WordTrace tailWord_3029816 prefixEnd_3029816 1037167935121882043110757 := by
  unfold tailWord_3029816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55253233995750779110750651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73670978661001038814334201 55253233995750779110750651)
  ·
    refine ⟨82879850993626168666125977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55253233995750779110750651 82879850993626168666125977)
    ·
      refine ⟨62159888245219626499594483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82879850993626168666125977 62159888245219626499594483)
      ·
        refine ⟨93239832367829439749391725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62159888245219626499594483 93239832367829439749391725)
        ·
          refine ⟨34964937137936039906021897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93239832367829439749391725 34964937137936039906021897)
          ·
            refine ⟨26223702853452029929516423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34964937137936039906021897 26223702853452029929516423)
            ·
              refine ⟨39335554280178044894274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26223702853452029929516423 39335554280178044894274635)
              ·
                refine ⟨59003331420267067341411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39335554280178044894274635 59003331420267067341411953)
                ·
                  refine ⟨44252498565200300506058965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59003331420267067341411953 44252498565200300506058965)
                  ·
                    refine ⟨1037167935121882043110757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44252498565200300506058965 1037167935121882043110757)
                    ·
                      rfl

theorem cell22_3029816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3029816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029816 prefixEnd_3029816 := by exact prefixLift 3029816
  have htrace : WordTrace (prefixWord ++ tailWord_3029816) baseStart_3029816 baseEnd_3029816 := by
    simpa [prefixWord, tailWord_3029816, baseEnd_3029816] using wordTrace_append hprefix tailTrace_3029816
  have hstable : (prefixWord ++ tailWord_3029816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029816).length < 2 ^ (prefixWord ++ tailWord_3029816).sum := by decide
  have hdescent : baseEnd_3029816 < baseStart_3029816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029818 : List Nat := [3, 1, 1, 1, 6, 1, 1, 8]
def baseStart_3029818 : Nat := 118140960795 + 3029818 * 2 ^ 59
def prefixEnd_3029818 : Nat := 4983230072969 + 3 ^ 40 * 3029818 * 2
def baseEnd_3029818 : Nat := 115240957751417189395639

theorem tailTrace_3029818 : CollatzResearch.WordTrace tailWord_3029818 prefixEnd_3029818 115240957751417189395639 := by
  unfold tailWord_3029818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626635234373578140768527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73671027291662875042049405 27626635234373578140768527)
  ·
    refine ⟨41439952851560367211152791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27626635234373578140768527 41439952851560367211152791)
    ·
      refine ⟨62159929277340550816729187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41439952851560367211152791 62159929277340550816729187)
      ·
        refine ⟨93239893916010826225093781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62159929277340550816729187 93239893916010826225093781)
        ·
          refine ⟨4370620027313007479301271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93239893916010826225093781 4370620027313007479301271)
          ·
            refine ⟨6555930040969511218951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370620027313007479301271 6555930040969511218951907)
            ·
              refine ⟨9833895061454266828427861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555930040969511218951907 9833895061454266828427861)
              ·
                refine ⟨115240957751417189395639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9833895061454266828427861 115240957751417189395639)
                ·
                  rfl

theorem cell22_3029818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_3029818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029818 prefixEnd_3029818 := by exact prefixLift 3029818
  have htrace : WordTrace (prefixWord ++ tailWord_3029818) baseStart_3029818 baseEnd_3029818 := by
    simpa [prefixWord, tailWord_3029818, baseEnd_3029818] using wordTrace_append hprefix tailTrace_3029818
  have hstable : (prefixWord ++ tailWord_3029818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029818).length < 2 ^ (prefixWord ++ tailWord_3029818).sum := by decide
  have hdescent : baseEnd_3029818 < baseStart_3029818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029831 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3029831 : Nat := 118140960795 + 3029831 * 2 ^ 59
def prefixEnd_3029831 : Nat := 4983230072969 + 3 ^ 40 * 3029831 * 2
def baseEnd_3029831 : Nat := 1037173069928427003985711

theorem tailTrace_3029831 : CollatzResearch.WordTrace tailWord_3029831 prefixEnd_3029831 1037173069928427003985711 := by
  unfold tailWord_3029831
  simp only [CollatzResearch.WordTrace]
  refine ⟨110507015086447215783297347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73671343390964810522198231 110507015086447215783297347)
  ·
    refine ⟨165760522629670823674946021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110507015086447215783297347 165760522629670823674946021)
    ·
      refine ⟨31080097993063279439052379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165760522629670823674946021 31080097993063279439052379)
      ·
        refine ⟨46620146989594919158578569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31080097993063279439052379 46620146989594919158578569)
        ·
          refine ⟨34965110242196189368933927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46620146989594919158578569 34965110242196189368933927)
          ·
            refine ⟨52447665363294284053400891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34965110242196189368933927 52447665363294284053400891)
            ·
              refine ⟨78671498044941426080101337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52447665363294284053400891 78671498044941426080101337)
              ·
                refine ⟨59003623533706069560076003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78671498044941426080101337 59003623533706069560076003)
                ·
                  refine ⟨88505435300559104340114005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59003623533706069560076003 88505435300559104340114005)
                  ·
                    refine ⟨1037173069928427003985711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88505435300559104340114005 1037173069928427003985711)
                    ·
                      rfl

theorem cell22_3029831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3029831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029831 prefixEnd_3029831 := by exact prefixLift 3029831
  have htrace : WordTrace (prefixWord ++ tailWord_3029831) baseStart_3029831 baseEnd_3029831 := by
    simpa [prefixWord, tailWord_3029831, baseEnd_3029831] using wordTrace_append hprefix tailTrace_3029831
  have hstable : (prefixWord ++ tailWord_3029831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029831).length < 2 ^ (prefixWord ++ tailWord_3029831).sum := by decide
  have hdescent : baseEnd_3029831 < baseStart_3029831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029837 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3029837 : Nat := 118140960795 + 3029837 * 2 ^ 59
def prefixEnd_3029837 : Nat := 4983230072969 + 3 ^ 40 * 3029837 * 2
def baseEnd_3029837 : Nat := 1037175123851044988335693

theorem tailTrace_3029837 : CollatzResearch.WordTrace tailWord_3029837 prefixEnd_3029837 1037175123851044988335693 := by
  unfold tailWord_3029837
  simp only [CollatzResearch.WordTrace]
  refine ⟨110507233924425478808015765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73671489282950319205343843 110507233924425478808015765)
  ·
    refine ⟨5180026590207444319125739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110507233924425478808015765 5180026590207444319125739)
    ·
      refine ⟨7770039885311166478688609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5180026590207444319125739 7770039885311166478688609)
      ·
        refine ⟨5827529913983374859016457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7770039885311166478688609 5827529913983374859016457)
        ·
          refine ⟨4370647435487531144262343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827529913983374859016457 4370647435487531144262343)
          ·
            refine ⟨6555971153231296716393515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370647435487531144262343 6555971153231296716393515)
            ·
              refine ⟨9833956729846945074590273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555971153231296716393515 9833956729846945074590273)
              ·
                refine ⟨7375467547385208805942705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9833956729846945074590273 7375467547385208805942705)
                ·
                  refine ⟨5531600660538906604457029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375467547385208805942705 5531600660538906604457029)
                  ·
                    refine ⟨1037175123851044988335693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5531600660538906604457029 1037175123851044988335693)
                    ·
                      rfl

theorem cell22_3029837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3029837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029837 prefixEnd_3029837 := by exact prefixLift 3029837
  have htrace : WordTrace (prefixWord ++ tailWord_3029837) baseStart_3029837 baseEnd_3029837 := by
    simpa [prefixWord, tailWord_3029837, baseEnd_3029837] using wordTrace_append hprefix tailTrace_3029837
  have hstable : (prefixWord ++ tailWord_3029837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029837).length < 2 ^ (prefixWord ++ tailWord_3029837).sum := by decide
  have hdescent : baseEnd_3029837 < baseStart_3029837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029850 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_3029850 : Nat := 118140960795 + 3029850 * 2 ^ 59
def prefixEnd_3029850 : Nat := 4983230072969 + 3 ^ 40 * 3029850 * 2
def baseEnd_3029850 : Nat := 1037179574016717287760653

theorem tailTrace_3029850 : CollatzResearch.WordTrace tailWord_3029850 prefixEnd_3029850 1037179574016717287760653 := by
  unfold tailWord_3029850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626927018344595507059751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73671805382252254685492669 27626927018344595507059751)
  ·
    refine ⟨41440390527516893260589627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27626927018344595507059751 41440390527516893260589627)
    ·
      refine ⟨62160585791275339890884441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41440390527516893260589627 62160585791275339890884441)
      ·
        refine ⟨46620439343456504918163331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62160585791275339890884441 46620439343456504918163331)
        ·
          refine ⟨69930659015184757377244997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46620439343456504918163331 69930659015184757377244997)
          ·
            refine ⟨13111998565347142008233437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69930659015184757377244997 13111998565347142008233437)
            ·
              refine ⟨4916999462005178253087539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13111998565347142008233437 4916999462005178253087539)
              ·
                refine ⟨7375499193007767379631309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916999462005178253087539 7375499193007767379631309)
                ·
                  refine ⟨2765812197377912767361741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7375499193007767379631309 2765812197377912767361741)
                  ·
                    refine ⟨1037179574016717287760653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765812197377912767361741 1037179574016717287760653)
                    ·
                      rfl

theorem cell22_3029850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_3029850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029850 prefixEnd_3029850 := by exact prefixLift 3029850
  have htrace : WordTrace (prefixWord ++ tailWord_3029850) baseStart_3029850 baseEnd_3029850 := by
    simpa [prefixWord, tailWord_3029850, baseEnd_3029850] using wordTrace_append hprefix tailTrace_3029850
  have hstable : (prefixWord ++ tailWord_3029850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029850).length < 2 ^ (prefixWord ++ tailWord_3029850).sum := by decide
  have hdescent : baseEnd_3029850 < baseStart_3029850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029923 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_3029923 : Nat := 118140960795 + 3029923 * 2 ^ 59
def prefixEnd_3029923 : Nat := 4983230072969 + 3 ^ 40 * 3029923 * 2
def baseEnd_3029923 : Nat := 1037204563408569430685429

theorem tailTrace_3029923 : CollatzResearch.WordTrace tailWord_3029923 prefixEnd_3029923 1037204563408569430685429 := by
  unfold tailWord_3029923
  simp only [CollatzResearch.WordTrace]
  refine ⟨110510370602113915495646423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73673580401409276997097615 110510370602113915495646423)
  ·
    refine ⟨165765555903170873243469635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110510370602113915495646423 165765555903170873243469635)
    ·
      refine ⟨248648333854756309865204453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165765555903170873243469635 248648333854756309865204453)
      ·
        refine ⟨46621562597766808099725835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248648333854756309865204453 46621562597766808099725835)
        ·
          refine ⟨69932343896650212149588753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46621562597766808099725835 69932343896650212149588753)
          ·
            refine ⟨52449257922487659112191565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69932343896650212149588753 52449257922487659112191565)
            ·
              refine ⟨19668471720932872167071837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52449257922487659112191565 19668471720932872167071837)
              ·
                refine ⟨7375676895349827062651939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19668471720932872167071837 7375676895349827062651939)
                ·
                  refine ⟨11063515343024740593977909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375676895349827062651939 11063515343024740593977909)
                  ·
                    refine ⟨1037204563408569430685429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11063515343024740593977909 1037204563408569430685429)
                    ·
                      rfl

theorem cell22_3029923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_3029923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029923 prefixEnd_3029923 := by exact prefixLift 3029923
  have htrace : WordTrace (prefixWord ++ tailWord_3029923) baseStart_3029923 baseEnd_3029923 := by
    simpa [prefixWord, tailWord_3029923, baseEnd_3029923] using wordTrace_append hprefix tailTrace_3029923
  have hstable : (prefixWord ++ tailWord_3029923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029923).length < 2 ^ (prefixWord ++ tailWord_3029923).sum := by decide
  have hdescent : baseEnd_3029923 < baseStart_3029923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029974 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3029974 : Nat := 118140960795 + 3029974 * 2 ^ 59
def prefixEnd_3029974 : Nat := 4983230072969 + 3 ^ 40 * 3029974 * 2
def baseEnd_3029974 : Nat := 1037222021750822297660273

theorem tailTrace_3029974 : CollatzResearch.WordTrace tailWord_3029974 prefixEnd_3029974 1037222021750822297660273 := by
  unfold tailWord_3029974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907014420308071950359561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73674820483286100803835317 6907014420308071950359561)
  ·
    refine ⟨5180260815231053962769671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6907014420308071950359561 5180260815231053962769671)
    ·
      refine ⟨7770391222846580944154507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5180260815231053962769671 7770391222846580944154507)
      ·
        refine ⟨11655586834269871416231761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7770391222846580944154507 11655586834269871416231761)
        ·
          refine ⟨8741690125702403562173821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11655586834269871416231761 8741690125702403562173821)
          ·
            refine ⟨3278133797138401335815183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8741690125702403562173821 3278133797138401335815183)
            ·
              refine ⟨4917200695707602003722775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278133797138401335815183 4917200695707602003722775)
              ·
                refine ⟨7375801043561403005584163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917200695707602003722775 7375801043561403005584163)
                ·
                  refine ⟨11063701565342104508376245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375801043561403005584163 11063701565342104508376245)
                  ·
                    refine ⟨1037222021750822297660273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11063701565342104508376245 1037222021750822297660273)
                    ·
                      rfl

theorem cell22_3029974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3029974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3029974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3029974 prefixEnd_3029974 := by exact prefixLift 3029974
  have htrace : WordTrace (prefixWord ++ tailWord_3029974) baseStart_3029974 baseEnd_3029974 := by
    simpa [prefixWord, tailWord_3029974, baseEnd_3029974] using wordTrace_append hprefix tailTrace_3029974
  have hstable : (prefixWord ++ tailWord_3029974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029974).length < 2 ^ (prefixWord ++ tailWord_3029974).sum := by decide
  have hdescent : baseEnd_3029974 < baseStart_3029974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030090 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3030090 : Nat := 118140960795 + 3030090 * 2 ^ 59
def prefixEnd_3030090 : Nat := 4983230072969 + 3 ^ 40 * 3030090 * 2
def baseEnd_3030090 : Nat := 1037261730921436661759917

theorem tailTrace_3030090 : CollatzResearch.WordTrace tailWord_3030090 prefixEnd_3030090 1037261730921436661759917 := by
  unfold tailWord_3030090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27629115398127225754243931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73677641061672602011317149 27629115398127225754243931)
  ·
    refine ⟨41443673097190838631365897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27629115398127225754243931 41443673097190838631365897)
    ·
      refine ⟨31082754822893128973524423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41443673097190838631365897 31082754822893128973524423)
      ·
        refine ⟨46624132234339693460286635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31082754822893128973524423 46624132234339693460286635)
        ·
          refine ⟨69936198351509540190429953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46624132234339693460286635 69936198351509540190429953)
          ·
            refine ⟨52452148763632155142822465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69936198351509540190429953 52452148763632155142822465)
            ·
              refine ⟨39339111572724116357116849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52452148763632155142822465 39339111572724116357116849)
              ·
                refine ⟨29504333679543087267837637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39339111572724116357116849 29504333679543087267837637)
                ·
                  refine ⟨5532062564914328862719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29504333679543087267837637 5532062564914328862719557)
                  ·
                    refine ⟨1037261730921436661759917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532062564914328862719557 1037261730921436661759917)
                    ·
                      rfl

theorem cell22_3030090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3030090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030090 prefixEnd_3030090 := by exact prefixLift 3030090
  have htrace : WordTrace (prefixWord ++ tailWord_3030090) baseStart_3030090 baseEnd_3030090 := by
    simpa [prefixWord, tailWord_3030090, baseEnd_3030090] using wordTrace_append hprefix tailTrace_3030090
  have hstable : (prefixWord ++ tailWord_3030090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030090).length < 2 ^ (prefixWord ++ tailWord_3030090).sum := by decide
  have hdescent : baseEnd_3030090 < baseStart_3030090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030126 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3030126 : Nat := 118140960795 + 3030126 * 2 ^ 59
def prefixEnd_3030126 : Nat := 4983230072969 + 3 ^ 40 * 3030126 * 2
def baseEnd_3030126 : Nat := 1037274054457144567859807

theorem tailTrace_3030126 : CollatzResearch.WordTrace tailWord_3030126 prefixEnd_3030126 1037274054457144567859807 := by
  unfold tailWord_3030126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814721827547310145660779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73678516413585654110190821 13814721827547310145660779)
  ·
    refine ⟨20722082741320965218491169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13814721827547310145660779 20722082741320965218491169)
    ·
      refine ⟨15541562055990723913868377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20722082741320965218491169 15541562055990723913868377)
      ·
        refine ⟨11656171541993042935401283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15541562055990723913868377 11656171541993042935401283)
        ·
          refine ⟨17484257312989564403101925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11656171541993042935401283 17484257312989564403101925)
          ·
            refine ⟨3278298246185543325581611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17484257312989564403101925 3278298246185543325581611)
            ·
              refine ⟨4917447369278314988372417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278298246185543325581611 4917447369278314988372417)
              ·
                refine ⟨3688085526958736241279313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4917447369278314988372417 3688085526958736241279313)
                ·
                  refine ⟨2766064145219052180959485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688085526958736241279313 2766064145219052180959485)
                  ·
                    refine ⟨1037274054457144567859807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766064145219052180959485 1037274054457144567859807)
                    ·
                      rfl

theorem cell22_3030126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3030126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030126 prefixEnd_3030126 := by exact prefixLift 3030126
  have htrace : WordTrace (prefixWord ++ tailWord_3030126) baseStart_3030126 baseEnd_3030126 := by
    simpa [prefixWord, tailWord_3030126, baseEnd_3030126] using wordTrace_append hprefix tailTrace_3030126
  have hstable : (prefixWord ++ tailWord_3030126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030126).length < 2 ^ (prefixWord ++ tailWord_3030126).sum := by decide
  have hdescent : baseEnd_3030126 < baseStart_3030126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030165 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3030165 : Nat := 118140960795 + 3030165 * 2 ^ 59
def prefixEnd_3030165 : Nat := 4983230072969 + 3 ^ 40 * 3030165 * 2
def baseEnd_3030165 : Nat := 1037287404954161466134687

theorem tailTrace_3030165 : CollatzResearch.WordTrace tailWord_3030165 prefixEnd_3030165 1037287404954161466134687 := by
  unfold tailWord_3030165
  simp only [CollatzResearch.WordTrace]
  refine ⟨110519197067237190825955949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73679464711491460550637299 110519197067237190825955949)
  ·
    refine ⟨41444698900213946559733481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110519197067237190825955949 41444698900213946559733481)
    ·
      refine ⟨31083524175160459919800111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41444698900213946559733481 31083524175160459919800111)
      ·
        refine ⟨46625286262740689879700167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31083524175160459919800111 46625286262740689879700167)
        ·
          refine ⟨69937929394111034819550251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46625286262740689879700167 69937929394111034819550251)
          ·
            refine ⟨104906894091166552229325377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69937929394111034819550251 104906894091166552229325377)
            ·
              refine ⟨78680170568374914171994033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104906894091166552229325377 78680170568374914171994033)
              ·
                refine ⟨59010127926281185628995525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78680170568374914171994033 59010127926281185628995525)
                ·
                  refine ⟨11064398986177722305436661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59010127926281185628995525 11064398986177722305436661)
                  ·
                    refine ⟨1037287404954161466134687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11064398986177722305436661 1037287404954161466134687)
                    ·
                      rfl

theorem cell22_3030165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3030165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030165 prefixEnd_3030165 := by exact prefixLift 3030165
  have htrace : WordTrace (prefixWord ++ tailWord_3030165) baseStart_3030165 baseEnd_3030165 := by
    simpa [prefixWord, tailWord_3030165, baseEnd_3030165] using wordTrace_append hprefix tailTrace_3030165
  have hstable : (prefixWord ++ tailWord_3030165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030165).length < 2 ^ (prefixWord ++ tailWord_3030165).sum := by decide
  have hdescent : baseEnd_3030165 < baseStart_3030165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030240 : List Nat := [2, 1, 1, 3, 1, 14]
def baseStart_3030240 : Nat := 118140960795 + 3030240 * 2 ^ 59
def prefixEnd_3030240 : Nat := 4983230072969 + 3 ^ 40 * 3030240 * 2
def baseEnd_3030240 : Nat := 12806334308480077413697

theorem tailTrace_3030240 : CollatzResearch.WordTrace tailWord_3030240 prefixEnd_3030240 12806334308480077413697 := by
  unfold tailWord_3030240
  simp only [CollatzResearch.WordTrace]
  refine ⟨55260966270982739317468087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73681288361310319089957449 55260966270982739317468087)
  ·
    refine ⟨82891449406474108976202131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55260966270982739317468087 82891449406474108976202131)
    ·
      refine ⟨124337174109711163464303197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82891449406474108976202131 124337174109711163464303197)
      ·
        refine ⟨46626440291141686299113699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124337174109711163464303197 46626440291141686299113699)
        ·
          refine ⟨69939660436712529448670549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46626440291141686299113699 69939660436712529448670549)
          ·
            refine ⟨12806334308480077413697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 69939660436712529448670549 12806334308480077413697)
            ·
              rfl

theorem cell22_3030240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 14].length) (baseStart_3030240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030240 prefixEnd_3030240 := by exact prefixLift 3030240
  have htrace : WordTrace (prefixWord ++ tailWord_3030240) baseStart_3030240 baseEnd_3030240 := by
    simpa [prefixWord, tailWord_3030240, baseEnd_3030240] using wordTrace_append hprefix tailTrace_3030240
  have hstable : (prefixWord ++ tailWord_3030240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030240).length < 2 ^ (prefixWord ++ tailWord_3030240).sum := by decide
  have hdescent : baseEnd_3030240 < baseStart_3030240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030244 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3030244 : Nat := 118140960795 + 3030244 * 2 ^ 59
def prefixEnd_3030244 : Nat := 4983230072969 + 3 ^ 40 * 3030244 * 2
def baseEnd_3030244 : Nat := 1037314448268631593409445

theorem tailTrace_3030244 : CollatzResearch.WordTrace tailWord_3030244 prefixEnd_3030244 1037314448268631593409445 := by
  unfold tailWord_3030244
  simp only [CollatzResearch.WordTrace]
  refine ⟨55261039216975493659040893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73681385622633991545387857 55261039216975493659040893)
  ·
    refine ⟨20722889706365810122140335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55261039216975493659040893 20722889706365810122140335)
    ·
      refine ⟨31084334559548715183210503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20722889706365810122140335 31084334559548715183210503)
      ·
        refine ⟨46626501839323072774815755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31084334559548715183210503 46626501839323072774815755)
        ·
          refine ⟨69939752758984609162223633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46626501839323072774815755 69939752758984609162223633)
          ·
            refine ⟨52454814569238456871667725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69939752758984609162223633 52454814569238456871667725)
            ·
              refine ⟨19670555463464421326875397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52454814569238456871667725 19670555463464421326875397)
              ·
                refine ⟨3688229149399578998789137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19670555463464421326875397 3688229149399578998789137)
                ·
                  refine ⟨2766171862049684249091853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688229149399578998789137 2766171862049684249091853)
                  ·
                    refine ⟨1037314448268631593409445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766171862049684249091853 1037314448268631593409445)
                    ·
                      rfl

theorem cell22_3030244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3030244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030244 prefixEnd_3030244 := by exact prefixLift 3030244
  have htrace : WordTrace (prefixWord ++ tailWord_3030244) baseStart_3030244 baseEnd_3030244 := by
    simpa [prefixWord, tailWord_3030244, baseEnd_3030244] using wordTrace_append hprefix tailTrace_3030244
  have hstable : (prefixWord ++ tailWord_3030244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030244).length < 2 ^ (prefixWord ++ tailWord_3030244).sum := by decide
  have hdescent : baseEnd_3030244 < baseStart_3030244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030276 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_3030276 : Nat := 118140960795 + 3030276 * 2 ^ 59
def prefixEnd_3030276 : Nat := 4983230072969 + 3 ^ 40 * 3030276 * 2
def baseEnd_3030276 : Nat := 1037325402522594176609347

theorem tailTrace_3030276 : CollatzResearch.WordTrace tailWord_3030276 prefixEnd_3030276 1037325402522594176609347 := by
  unfold tailWord_3030276
  simp only [CollatzResearch.WordTrace]
  refine ⟨55261622784917528391623341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73682163713223371188831121 55261622784917528391623341)
  ·
    refine ⟨20723108544344073146858753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55261622784917528391623341 20723108544344073146858753)
    ·
      refine ⟨15542331408258054860144065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20723108544344073146858753 15542331408258054860144065)
      ·
        refine ⟨11656748556193541145108049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15542331408258054860144065 11656748556193541145108049)
        ·
          refine ⟨8742561417145155858831037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11656748556193541145108049 8742561417145155858831037)
          ·
            refine ⟨3278460531429433447061639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8742561417145155858831037 3278460531429433447061639)
            ·
              refine ⟨4917690797144150170592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278460531429433447061639 4917690797144150170592459)
              ·
                refine ⟨7376536195716225255888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917690797144150170592459 7376536195716225255888689)
                ·
                  refine ⟨5532402146787168941916517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7376536195716225255888689 5532402146787168941916517)
                  ·
                    refine ⟨1037325402522594176609347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532402146787168941916517 1037325402522594176609347)
                    ·
                      rfl

theorem cell22_3030276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_3030276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030276 prefixEnd_3030276 := by exact prefixLift 3030276
  have htrace : WordTrace (prefixWord ++ tailWord_3030276) baseStart_3030276 baseEnd_3030276 := by
    simpa [prefixWord, tailWord_3030276, baseEnd_3030276] using wordTrace_append hprefix tailTrace_3030276
  have hstable : (prefixWord ++ tailWord_3030276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030276).length < 2 ^ (prefixWord ++ tailWord_3030276).sum := by decide
  have hdescent : baseEnd_3030276 < baseStart_3030276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030340 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3030340 : Nat := 118140960795 + 3030340 * 2 ^ 59
def prefixEnd_3030340 : Nat := 4983230072969 + 3 ^ 40 * 3030340 * 2
def baseEnd_3030340 : Nat := 1037347311030519343009151

theorem tailTrace_3030340 : CollatzResearch.WordTrace tailWord_3030340 prefixEnd_3030340 1037347311030519343009151 := by
  unfold tailWord_3030340
  simp only [CollatzResearch.WordTrace]
  refine ⟨55262789920801597856788237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73683719894402130475717649 55262789920801597856788237)
  ·
    refine ⟨20723546220300599196295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55262789920801597856788237 20723546220300599196295589)
    ·
      refine ⟨3885664916306362349305423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20723546220300599196295589 3885664916306362349305423)
      ·
        refine ⟨5828497374459543523958135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885664916306362349305423 5828497374459543523958135)
        ·
          refine ⟨8742746061689315285937203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828497374459543523958135 8742746061689315285937203)
          ·
            refine ⟨13114119092533972928905805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8742746061689315285937203 13114119092533972928905805)
            ·
              refine ⟨4917794659700239848339677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13114119092533972928905805 4917794659700239848339677)
              ·
                refine ⟨1844172997387589943127379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4917794659700239848339677 1844172997387589943127379)
                ·
                  refine ⟨2766259496081384914691069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844172997387589943127379 2766259496081384914691069)
                  ·
                    refine ⟨1037347311030519343009151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766259496081384914691069 1037347311030519343009151)
                    ·
                      rfl

theorem cell22_3030340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3030340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030340 prefixEnd_3030340 := by exact prefixLift 3030340
  have htrace : WordTrace (prefixWord ++ tailWord_3030340) baseStart_3030340 baseEnd_3030340 := by
    simpa [prefixWord, tailWord_3030340, baseEnd_3030340] using wordTrace_append hprefix tailTrace_3030340
  have hstable : (prefixWord ++ tailWord_3030340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030340).length < 2 ^ (prefixWord ++ tailWord_3030340).sum := by decide
  have hdescent : baseEnd_3030340 < baseStart_3030340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030377 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_3030377 : Nat := 118140960795 + 3030377 * 2 ^ 59
def prefixEnd_3030377 : Nat := 4983230072969 + 3 ^ 40 * 3030377 * 2
def baseEnd_3030377 : Nat := 1037359976886663579834037

theorem tailTrace_3030377 : CollatzResearch.WordTrace tailWord_3030377 prefixEnd_3030377 1037359976886663579834037 := by
  unfold tailWord_3030377
  simp only [CollatzResearch.WordTrace]
  refine ⟨110526929342469151032673385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73684619561646100688448923 110526929342469151032673385)
  ·
    refine ⟨82895197006851863274505039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110526929342469151032673385 82895197006851863274505039)
    ·
      refine ⟨124342795510277794911757559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82895197006851863274505039 124342795510277794911757559)
      ·
        refine ⟨186514193265416692367636339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124342795510277794911757559 186514193265416692367636339)
        ·
          refine ⟨279771289898125038551454509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186514193265416692367636339 279771289898125038551454509)
          ·
            refine ⟨104914233711796889456795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279771289898125038551454509 104914233711796889456795441)
            ·
              refine ⟨78685675283847667092596581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104914233711796889456795441 78685675283847667092596581)
              ·
                refine ⟨14753564115721437579861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78685675283847667092596581 14753564115721437579861859)
                ·
                  refine ⟨22130346173582156369792789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14753564115721437579861859 22130346173582156369792789)
                  ·
                    refine ⟨1037359976886663579834037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22130346173582156369792789 1037359976886663579834037)
                    ·
                      rfl

theorem cell22_3030377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_3030377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030377 prefixEnd_3030377 := by exact prefixLift 3030377
  have htrace : WordTrace (prefixWord ++ tailWord_3030377) baseStart_3030377 baseEnd_3030377 := by
    simpa [prefixWord, tailWord_3030377, baseEnd_3030377] using wordTrace_append hprefix tailTrace_3030377
  have hstable : (prefixWord ++ tailWord_3030377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030377).length < 2 ^ (prefixWord ++ tailWord_3030377).sum := by decide
  have hdescent : baseEnd_3030377 < baseStart_3030377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030409 : List Nat := [1, 2, 1, 1, 8, 9]
def baseStart_3030409 : Nat := 118140960795 + 3030409 * 2 ^ 59
def prefixEnd_3030409 : Nat := 4983230072969 + 3 ^ 40 * 3030409 * 2
def baseEnd_3030409 : Nat := 12807048532600323000419

theorem tailTrace_3030409 : CollatzResearch.WordTrace tailWord_3030409 prefixEnd_3030409 12807048532600323000419 := by
  unfold tailWord_3030409
  simp only [CollatzResearch.WordTrace]
  refine ⟨110528096478353220497838281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73685397652235480331892187 110528096478353220497838281)
  ·
    refine ⟨82896072358764915373378711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110528096478353220497838281 82896072358764915373378711)
    ·
      refine ⟨124344108538147373060068067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82896072358764915373378711 124344108538147373060068067)
      ·
        refine ⟨186516162807221059590102101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124344108538147373060068067 186516162807221059590102101)
        ·
          refine ⟨2185736282897121792071509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 186516162807221059590102101 2185736282897121792071509)
          ·
            refine ⟨12807048532600323000419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2185736282897121792071509 12807048532600323000419)
            ·
              rfl

theorem cell22_3030409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 9].length) (baseStart_3030409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030409 prefixEnd_3030409 := by exact prefixLift 3030409
  have htrace : WordTrace (prefixWord ++ tailWord_3030409) baseStart_3030409 baseEnd_3030409 := by
    simpa [prefixWord, tailWord_3030409, baseEnd_3030409] using wordTrace_append hprefix tailTrace_3030409
  have hstable : (prefixWord ++ tailWord_3030409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030409).length < 2 ^ (prefixWord ++ tailWord_3030409).sum := by decide
  have hdescent : baseEnd_3030409 < baseStart_3030409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030439 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3030439 : Nat := 118140960795 + 3030439 * 2 ^ 59
def prefixEnd_3030439 : Nat := 4983230072969 + 3 ^ 40 * 3030439 * 2
def baseEnd_3030439 : Nat := 1037381200753716084783847

theorem tailTrace_3030439 : CollatzResearch.WordTrace tailWord_3030439 prefixEnd_3030439 1037381200753716084783847 := by
  unfold tailWord_3030439
  simp only [CollatzResearch.WordTrace]
  refine ⟨110529190668244535621430371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73686127112163023747620247 110529190668244535621430371)
  ·
    refine ⟨165793786002366803432145557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110529190668244535621430371 165793786002366803432145557)
    ·
      refine ⟨7771583718860943910881823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165793786002366803432145557 7771583718860943910881823)
      ·
        refine ⟨11657375578291415866322735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771583718860943910881823 11657375578291415866322735)
        ·
          refine ⟨17486063367437123799484103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11657375578291415866322735 17486063367437123799484103)
          ·
            refine ⟨26229095051155685699226155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17486063367437123799484103 26229095051155685699226155)
            ·
              refine ⟨39343642576733528548839233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26229095051155685699226155 39343642576733528548839233)
              ·
                refine ⟨29507731932550146411629425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39343642576733528548839233 29507731932550146411629425)
                ·
                  refine ⟨22130798949412609808722069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29507731932550146411629425 22130798949412609808722069)
                  ·
                    refine ⟨1037381200753716084783847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22130798949412609808722069 1037381200753716084783847)
                    ·
                      rfl

theorem cell22_3030439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3030439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030439 prefixEnd_3030439 := by exact prefixLift 3030439
  have htrace : WordTrace (prefixWord ++ tailWord_3030439) baseStart_3030439 baseEnd_3030439 := by
    simpa [prefixWord, tailWord_3030439, baseEnd_3030439] using wordTrace_append hprefix tailTrace_3030439
  have hstable : (prefixWord ++ tailWord_3030439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030439).length < 2 ^ (prefixWord ++ tailWord_3030439).sum := by decide
  have hdescent : baseEnd_3030439 < baseStart_3030439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030509 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3030509 : Nat := 118140960795 + 3030509 * 2 ^ 59
def prefixEnd_3030509 : Nat := 4983230072969 + 3 ^ 40 * 3030509 * 2
def baseEnd_3030509 : Nat := 1037405163184259235533633

theorem tailTrace_3030509 : CollatzResearch.WordTrace tailWord_3030509 prefixEnd_3030509 1037405163184259235533633 := by
  unfold tailWord_3030509
  simp only [CollatzResearch.WordTrace]
  refine ⟨110531743777990937576478581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73687829185327291717652387 110531743777990937576478581)
  ·
    refine ⟨10362350979186650397794867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110531743777990937576478581 10362350979186650397794867)
    ·
      refine ⟨15543526468779975596692301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362350979186650397794867 15543526468779975596692301)
      ·
        refine ⟨5828822425792490848759613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15543526468779975596692301 5828822425792490848759613)
        ·
          refine ⟨2185808409672184068284855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5828822425792490848759613 2185808409672184068284855)
          ·
            refine ⟨3278712614508276102427283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185808409672184068284855 3278712614508276102427283)
            ·
              refine ⟨4918068921762414153640925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278712614508276102427283 4918068921762414153640925)
              ·
                refine ⟨1844275845660905307615347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4918068921762414153640925 1844275845660905307615347)
                ·
                  refine ⟨2766413768491357961423021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844275845660905307615347 2766413768491357961423021)
                  ·
                    refine ⟨1037405163184259235533633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766413768491357961423021 1037405163184259235533633)
                    ·
                      rfl

theorem cell22_3030509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3030509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030509 prefixEnd_3030509 := by exact prefixLift 3030509
  have htrace : WordTrace (prefixWord ++ tailWord_3030509) baseStart_3030509 baseEnd_3030509 := by
    simpa [prefixWord, tailWord_3030509, baseEnd_3030509] using wordTrace_append hprefix tailTrace_3030509
  have hstable : (prefixWord ++ tailWord_3030509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030509).length < 2 ^ (prefixWord ++ tailWord_3030509).sum := by decide
  have hdescent : baseEnd_3030509 < baseStart_3030509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030518 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3030518 : Nat := 118140960795 + 3030518 * 2 ^ 59
def prefixEnd_3030518 : Nat := 4983230072969 + 3 ^ 40 * 3030518 * 2
def baseEnd_3030518 : Nat := 1037408244068186212058605

theorem tailTrace_3030518 : CollatzResearch.WordTrace tailWord_3030518 prefixEnd_3030518 1037408244068186212058605 := by
  unfold tailWord_3030518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908254502184895757097263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73688048023305554742370805 6908254502184895757097263)
  ·
    refine ⟨10362381753277343635645895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908254502184895757097263 10362381753277343635645895)
    ·
      refine ⟨15543572629916015453468843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362381753277343635645895 15543572629916015453468843)
      ·
        refine ⟨23315358944874023180203265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15543572629916015453468843 23315358944874023180203265)
        ·
          refine ⟨17486519208655517385152449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23315358944874023180203265 17486519208655517385152449)
          ·
            refine ⟨13114889406491638038864337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17486519208655517385152449 13114889406491638038864337)
            ·
              refine ⟨9836167054868728529148253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13114889406491638038864337 9836167054868728529148253)
              ·
                refine ⟨3688562645575773198430595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9836167054868728529148253 3688562645575773198430595)
                ·
                  refine ⟨5532843968363659797645893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688562645575773198430595 5532843968363659797645893)
                  ·
                    refine ⟨1037408244068186212058605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532843968363659797645893 1037408244068186212058605)
                    ·
                      rfl

theorem cell22_3030518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3030518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030518 prefixEnd_3030518 := by exact prefixLift 3030518
  have htrace : WordTrace (prefixWord ++ tailWord_3030518) baseStart_3030518 baseEnd_3030518 := by
    simpa [prefixWord, tailWord_3030518, baseEnd_3030518] using wordTrace_append hprefix tailTrace_3030518
  have hstable : (prefixWord ++ tailWord_3030518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030518).length < 2 ^ (prefixWord ++ tailWord_3030518).sum := by decide
  have hdescent : baseEnd_3030518 < baseStart_3030518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030559 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3030559 : Nat := 118140960795 + 3030559 * 2 ^ 59
def prefixEnd_3030559 : Nat := 4983230072969 + 3 ^ 40 * 3030559 * 2
def baseEnd_3030559 : Nat := 1037422279206075771783479

theorem tailTrace_3030559 : CollatzResearch.WordTrace tailWord_3030559 prefixEnd_3030559 1037422279206075771783479 := by
  unfold tailWord_3030559
  simp only [CollatzResearch.WordTrace]
  refine ⟨110533567427809796115798731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73689044951873197410532487 110533567427809796115798731)
  ·
    refine ⟨165800351141714694173698097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110533567427809796115798731 165800351141714694173698097)
    ·
      refine ⟨124350263356286020630273573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165800351141714694173698097 124350263356286020630273573)
      ·
        refine ⟨23315674379303628868176295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124350263356286020630273573 23315674379303628868176295)
        ·
          refine ⟨34973511568955443302264443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23315674379303628868176295 34973511568955443302264443)
          ·
            refine ⟨52460267353433164953396665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34973511568955443302264443 52460267353433164953396665)
            ·
              refine ⟨39345200515074873715047499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52460267353433164953396665 39345200515074873715047499)
              ·
                refine ⟨59017800772612310572571249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39345200515074873715047499 59017800772612310572571249)
                ·
                  refine ⟨44263350579459232929428437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59017800772612310572571249 44263350579459232929428437)
                  ·
                    refine ⟨1037422279206075771783479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44263350579459232929428437 1037422279206075771783479)
                    ·
                      rfl

theorem cell22_3030559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3030559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030559 prefixEnd_3030559 := by exact prefixLift 3030559
  have htrace : WordTrace (prefixWord ++ tailWord_3030559) baseStart_3030559 baseEnd_3030559 := by
    simpa [prefixWord, tailWord_3030559, baseEnd_3030559] using wordTrace_append hprefix tailTrace_3030559
  have hstable : (prefixWord ++ tailWord_3030559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030559).length < 2 ^ (prefixWord ++ tailWord_3030559).sum := by decide
  have hdescent : baseEnd_3030559 < baseStart_3030559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030563 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_3030563 : Nat := 118140960795 + 3030563 * 2 ^ 59
def prefixEnd_3030563 : Nat := 4983230072969 + 3 ^ 40 * 3030563 * 2
def baseEnd_3030563 : Nat := 1037423648487821094683467

theorem tailTrace_3030563 : CollatzResearch.WordTrace tailWord_3030563 prefixEnd_3030563 1037423648487821094683467 := by
  unfold tailWord_3030563
  simp only [CollatzResearch.WordTrace]
  refine ⟨110533713319795304798944343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73689142213196869865962895 110533713319795304798944343)
  ·
    refine ⟨165800569979692957198416515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110533713319795304798944343 165800569979692957198416515)
    ·
      refine ⟨248700854969539435797624773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165800569979692957198416515 248700854969539435797624773)
      ·
        refine ⟨46631410306788644212054645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248700854969539435797624773 46631410306788644212054645)
        ·
          refine ⟨4371694716261435394880123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46631410306788644212054645 4371694716261435394880123)
          ·
            refine ⟨6557542074392153092320185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371694716261435394880123 6557542074392153092320185)
            ·
              refine ⟨4918156555794114819240139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6557542074392153092320185 4918156555794114819240139)
              ·
                refine ⟨7377234833691172228860209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918156555794114819240139 7377234833691172228860209)
                ·
                  refine ⟨5532926125268379171645157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377234833691172228860209 5532926125268379171645157)
                  ·
                    refine ⟨1037423648487821094683467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532926125268379171645157 1037423648487821094683467)
                    ·
                      rfl

theorem cell22_3030563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_3030563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030563 prefixEnd_3030563 := by exact prefixLift 3030563
  have htrace : WordTrace (prefixWord ++ tailWord_3030563) baseStart_3030563 baseEnd_3030563 := by
    simpa [prefixWord, tailWord_3030563, baseEnd_3030563] using wordTrace_append hprefix tailTrace_3030563
  have hstable : (prefixWord ++ tailWord_3030563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030563).length < 2 ^ (prefixWord ++ tailWord_3030563).sum := by decide
  have hdescent : baseEnd_3030563 < baseStart_3030563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030582 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3030582 : Nat := 118140960795 + 3030582 * 2 ^ 59
def prefixEnd_3030582 : Nat := 4983230072969 + 3 ^ 40 * 3030582 * 2
def baseEnd_3030582 : Nat := 1037430152576111378458409

theorem tailTrace_3030582 : CollatzResearch.WordTrace tailWord_3030582 prefixEnd_3030582 1037430152576111378458409 := by
  unfold tailWord_3030582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908400394170404440242875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73689604204484314029257333 6908400394170404440242875)
  ·
    refine ⟨10362600591255606660364313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908400394170404440242875 10362600591255606660364313)
    ·
      refine ⟨7771950443441704995273235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10362600591255606660364313 7771950443441704995273235)
      ·
        refine ⟨11657925665162557492909853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771950443441704995273235 11657925665162557492909853)
        ·
          refine ⟨4371722124435959059841195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11657925665162557492909853 4371722124435959059841195)
          ·
            refine ⟨6557583186653938589761793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371722124435959059841195 6557583186653938589761793)
            ·
              refine ⟨4918187389990453942321345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6557583186653938589761793 4918187389990453942321345)
              ·
                refine ⟨3688640542492840456741009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918187389990453942321345 3688640542492840456741009)
                ·
                  refine ⟨2766480406869630342555757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688640542492840456741009 2766480406869630342555757)
                  ·
                    refine ⟨1037430152576111378458409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766480406869630342555757 1037430152576111378458409)
                    ·
                      rfl

theorem cell22_3030582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3030582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030582 prefixEnd_3030582 := by exact prefixLift 3030582
  have htrace : WordTrace (prefixWord ++ tailWord_3030582) baseStart_3030582 baseEnd_3030582 := by
    simpa [prefixWord, tailWord_3030582, baseEnd_3030582] using wordTrace_append hprefix tailTrace_3030582
  have hstable : (prefixWord ++ tailWord_3030582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030582).length < 2 ^ (prefixWord ++ tailWord_3030582).sum := by decide
  have hdescent : baseEnd_3030582 < baseStart_3030582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030593 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3030593 : Nat := 118140960795 + 3030593 * 2 ^ 59
def prefixEnd_3030593 : Nat := 4983230072969 + 3 ^ 40 * 3030593 * 2
def baseEnd_3030593 : Nat := 1037433918100911016433375

theorem tailTrace_3030593 : CollatzResearch.WordTrace tailWord_3030593 prefixEnd_3030593 1037433918100911016433375 := by
  unfold tailWord_3030593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110534807509686619922536433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73689871673124413281690955 110534807509686619922536433)
  ·
    refine ⟨82901105632264964941902325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110534807509686619922536433 82901105632264964941902325)
    ·
      refine ⟨7771978653024840463303343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82901105632264964941902325 7771978653024840463303343)
      ·
        refine ⟨11657967979537260694955015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771978653024840463303343 11657967979537260694955015)
        ·
          refine ⟨17486951969305891042432523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11657967979537260694955015 17486951969305891042432523)
          ·
            refine ⟨26230427953958836563648785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17486951969305891042432523 26230427953958836563648785)
            ·
              refine ⟨19672820965469127422736589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26230427953958836563648785 19672820965469127422736589)
              ·
                refine ⟨7377307862050922783526221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19672820965469127422736589 7377307862050922783526221)
                ·
                  refine ⟨2766490448269096043822333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7377307862050922783526221 2766490448269096043822333)
                  ·
                    refine ⟨1037433918100911016433375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766490448269096043822333 1037433918100911016433375)
                    ·
                      rfl

theorem cell22_3030593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3030593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030593 prefixEnd_3030593 := by exact prefixLift 3030593
  have htrace : WordTrace (prefixWord ++ tailWord_3030593) baseStart_3030593 baseEnd_3030593 := by
    simpa [prefixWord, tailWord_3030593, baseEnd_3030593] using wordTrace_append hprefix tailTrace_3030593
  have hstable : (prefixWord ++ tailWord_3030593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030593).length < 2 ^ (prefixWord ++ tailWord_3030593).sum := by decide
  have hdescent : baseEnd_3030593 < baseStart_3030593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030614 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3030614 : Nat := 118140960795 + 3030614 * 2 ^ 59
def prefixEnd_3030614 : Nat := 4983230072969 + 3 ^ 40 * 3030614 * 2
def baseEnd_3030614 : Nat := 1037441106830073961658311

theorem tailTrace_3030614 : CollatzResearch.WordTrace tailWord_3030614 prefixEnd_3030614 1037441106830073961658311 := by
  unfold tailWord_3030614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908473340163158781815681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73690382295073693672700597 6908473340163158781815681)
  ·
    refine ⟨5181355005122369086361761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6908473340163158781815681 5181355005122369086361761)
    ·
      refine ⟨3886016253841776814771321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5181355005122369086361761 3886016253841776814771321)
      ·
        refine ⟨2914512190381332611078491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3886016253841776814771321 2914512190381332611078491)
        ·
          refine ⟨4371768285571998916617737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914512190381332611078491 4371768285571998916617737)
          ·
            refine ⟨3278826214178999187463303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371768285571998916617737 3278826214178999187463303)
            ·
              refine ⟨4918239321268498781194955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278826214178999187463303 4918239321268498781194955)
              ·
                refine ⟨7377358981902748171792433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918239321268498781194955 7377358981902748171792433)
                ·
                  refine ⟨5533019236427061128844325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377358981902748171792433 5533019236427061128844325)
                  ·
                    refine ⟨1037441106830073961658311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533019236427061128844325 1037441106830073961658311)
                    ·
                      rfl

theorem cell22_3030614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3030614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030614 prefixEnd_3030614 := by exact prefixLift 3030614
  have htrace : WordTrace (prefixWord ++ tailWord_3030614) baseStart_3030614 baseEnd_3030614 := by
    simpa [prefixWord, tailWord_3030614, baseEnd_3030614] using wordTrace_append hprefix tailTrace_3030614
  have hstable : (prefixWord ++ tailWord_3030614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030614).length < 2 ^ (prefixWord ++ tailWord_3030614).sum := by decide
  have hdescent : baseEnd_3030614 < baseStart_3030614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030651 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 6]
def baseStart_3030651 : Nat := 118140960795 + 3030651 * 2 ^ 59
def prefixEnd_3030651 : Nat := 4983230072969 + 3 ^ 40 * 3030651 * 2
def baseEnd_3030651 : Nat := 345817924228739399494399

theorem tailTrace_3030651 : CollatzResearch.WordTrace tailWord_3030651 prefixEnd_3030651 345817924228739399494399 := by
  unfold tailWord_3030651
  simp only [CollatzResearch.WordTrace]
  refine ⟨110536922943476495828147807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73691281962317663885431871 110536922943476495828147807)
  ·
    refine ⟨165805384415214743742221711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110536922943476495828147807 165805384415214743742221711)
    ·
      refine ⟨248708076622822115613332567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165805384415214743742221711 248708076622822115613332567)
      ·
        refine ⟨373062114934233173419998851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248708076622822115613332567 373062114934233173419998851)
        ·
          refine ⟨559593172401349760129998277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373062114934233173419998851 559593172401349760129998277)
          ·
            refine ⟨104923719825253080024374677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 559593172401349760129998277 104923719825253080024374677)
            ·
              refine ⟨4918299366808738126142563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104923719825253080024374677 4918299366808738126142563)
              ·
                refine ⟨7377449050213107189213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918299366808738126142563 7377449050213107189213845)
                ·
                  refine ⟨345817924228739399494399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7377449050213107189213845 345817924228739399494399)
                  ·
                    rfl

theorem cell22_3030651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_3030651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030651 prefixEnd_3030651 := by exact prefixLift 3030651
  have htrace : WordTrace (prefixWord ++ tailWord_3030651) baseStart_3030651 baseEnd_3030651 := by
    simpa [prefixWord, tailWord_3030651, baseEnd_3030651] using wordTrace_append hprefix tailTrace_3030651
  have hstable : (prefixWord ++ tailWord_3030651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030651).length < 2 ^ (prefixWord ++ tailWord_3030651).sum := by decide
  have hdescent : baseEnd_3030651 < baseStart_3030651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030670 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3030670 : Nat := 118140960795 + 3030670 * 2 ^ 59
def prefixEnd_3030670 : Nat := 4983230072969 + 3 ^ 40 * 3030670 * 2
def baseEnd_3030670 : Nat := 1037460276774508482258139

theorem tailTrace_3030670 : CollatzResearch.WordTrace tailWord_3030670 prefixEnd_3030670 1037460276774508482258139 := by
  unfold tailWord_3030670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817201991300957759136183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73691743953605108048726309 13817201991300957759136183)
  ·
    refine ⟨20725802986951436638704275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817201991300957759136183 20725802986951436638704275)
    ·
      refine ⟨31088704480427154958056413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20725802986951436638704275 31088704480427154958056413)
      ·
        refine ⟨11658264180160183109271155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31088704480427154958056413 11658264180160183109271155)
        ·
          refine ⟨17487396270240274663906733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658264180160183109271155 17487396270240274663906733)
          ·
            refine ⟨6557773601340102998965025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17487396270240274663906733 6557773601340102998965025)
            ·
              refine ⟨4918330201005077249223769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6557773601340102998965025 4918330201005077249223769)
              ·
                refine ⟨3688747650753807936917827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918330201005077249223769 3688747650753807936917827)
                ·
                  refine ⟨5533121476130711905376741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688747650753807936917827 5533121476130711905376741)
                  ·
                    refine ⟨1037460276774508482258139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533121476130711905376741 1037460276774508482258139)
                    ·
                      rfl

theorem cell22_3030670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3030670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030670 prefixEnd_3030670 := by exact prefixLift 3030670
  have htrace : WordTrace (prefixWord ++ tailWord_3030670) baseStart_3030670 baseEnd_3030670 := by
    simpa [prefixWord, tailWord_3030670, baseEnd_3030670] using wordTrace_append hprefix tailTrace_3030670
  have hstable : (prefixWord ++ tailWord_3030670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030670).length < 2 ^ (prefixWord ++ tailWord_3030670).sum := by decide
  have hdescent : baseEnd_3030670 < baseStart_3030670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030702 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_3030702 : Nat := 118140960795 + 3030702 * 2 ^ 59
def prefixEnd_3030702 : Nat := 4983230072969 + 3 ^ 40 * 3030702 * 2
def baseEnd_3030702 : Nat := 345823743676157021819347

theorem tailTrace_3030702 : CollatzResearch.WordTrace tailWord_3030702 prefixEnd_3030702 345823743676157021819347 := by
  unfold tailWord_3030702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817347883286466442281795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73692522044194487692169573 13817347883286466442281795)
  ·
    refine ⟨20726021824929699663422693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817347883286466442281795 20726021824929699663422693)
    ·
      refine ⟨3886129092174318686891755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20726021824929699663422693 3886129092174318686891755)
      ·
        refine ⟨5829193638261478030337633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886129092174318686891755 5829193638261478030337633)
        ·
          refine ⟨4371895228696108522753225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5829193638261478030337633 4371895228696108522753225)
          ·
            refine ⟨3278921421522081392064919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371895228696108522753225 3278921421522081392064919)
            ·
              refine ⟨4918382132283122088097379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278921421522081392064919 4918382132283122088097379)
              ·
                refine ⟨7377573198424683132146069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918382132283122088097379 7377573198424683132146069)
                ·
                  refine ⟨345823743676157021819347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7377573198424683132146069 345823743676157021819347)
                  ·
                    rfl

theorem cell22_3030702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_3030702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030702 prefixEnd_3030702 := by exact prefixLift 3030702
  have htrace : WordTrace (prefixWord ++ tailWord_3030702) baseStart_3030702 baseEnd_3030702 := by
    simpa [prefixWord, tailWord_3030702, baseEnd_3030702] using wordTrace_append hprefix tailTrace_3030702
  have hstable : (prefixWord ++ tailWord_3030702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030702).length < 2 ^ (prefixWord ++ tailWord_3030702).sum := by decide
  have hdescent : baseEnd_3030702 < baseStart_3030702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030728 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3030728 : Nat := 118140960795 + 3030728 * 2 ^ 59
def prefixEnd_3030728 : Nat := 4983230072969 + 3 ^ 40 * 3030728 * 2
def baseEnd_3030728 : Nat := 1037480131359815664307961

theorem tailTrace_3030728 : CollatzResearch.WordTrace tailWord_3030728 prefixEnd_3030728 1037480131359815664307961 := by
  unfold tailWord_3030728
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269865682098768989350419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73693154242798358652467225 55269865682098768989350419)
  ·
    refine ⟨82904798523148153484025629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55269865682098768989350419 82904798523148153484025629)
    ·
      refine ⟨31089299446180557556509611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82904798523148153484025629 31089299446180557556509611)
      ·
        refine ⟨46633949169270836334764417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31089299446180557556509611 46633949169270836334764417)
        ·
          refine ⟨34975461876953127251073313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46633949169270836334764417 34975461876953127251073313)
          ·
            refine ⟨26231596407714845438304985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34975461876953127251073313 26231596407714845438304985)
            ·
              refine ⟨19673697305786134078728739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26231596407714845438304985 19673697305786134078728739)
              ·
                refine ⟨29510545958679201118093109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19673697305786134078728739 29510545958679201118093109)
                ·
                  refine ⟨2766613683626175104821229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29510545958679201118093109 2766613683626175104821229)
                  ·
                    refine ⟨1037480131359815664307961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766613683626175104821229 1037480131359815664307961)
                    ·
                      rfl

theorem cell22_3030728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3030728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030728 prefixEnd_3030728 := by exact prefixLift 3030728
  have htrace : WordTrace (prefixWord ++ tailWord_3030728) baseStart_3030728 baseEnd_3030728 := by
    simpa [prefixWord, tailWord_3030728, baseEnd_3030728] using wordTrace_append hprefix tailTrace_3030728
  have hstable : (prefixWord ++ tailWord_3030728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030728).length < 2 ^ (prefixWord ++ tailWord_3030728).sum := by decide
  have hdescent : baseEnd_3030728 < baseStart_3030728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030805 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3030805 : Nat := 118140960795 + 3030805 * 2 ^ 59
def prefixEnd_3030805 : Nat := 4983230072969 + 3 ^ 40 * 3030805 * 2
def baseEnd_3030805 : Nat := 1037506490033413130132725

theorem tailTrace_3030805 : CollatzResearch.WordTrace tailWord_3030805 prefixEnd_3030805 1037506490033413130132725 := by
  unfold tailWord_3030805
  simp only [CollatzResearch.WordTrace]
  refine ⟨110542539784918580129253869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73695026523279053419502579 110542539784918580129253869)
  ·
    refine ⟨41453452419344467548470201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110542539784918580129253869 41453452419344467548470201)
    ·
      refine ⟨31090089314508350661352651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41453452419344467548470201 31090089314508350661352651)
      ·
        refine ⟨46635133971762525992028977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31090089314508350661352651 46635133971762525992028977)
        ·
          refine ⟨34976350478821894494021733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46635133971762525992028977 34976350478821894494021733)
          ·
            refine ⟨6558065714779105217629075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34976350478821894494021733 6558065714779105217629075)
            ·
              refine ⟨9837098572168657826443613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558065714779105217629075 9837098572168657826443613)
              ·
                refine ⟨3688911964563246684916355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9837098572168657826443613 3688911964563246684916355)
                ·
                  refine ⟨5533367946844870027374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688911964563246684916355 5533367946844870027374533)
                  ·
                    refine ⟨1037506490033413130132725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533367946844870027374533 1037506490033413130132725)
                    ·
                      rfl

theorem cell22_3030805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3030805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030805 prefixEnd_3030805 := by exact prefixLift 3030805
  have htrace : WordTrace (prefixWord ++ tailWord_3030805) baseStart_3030805 baseEnd_3030805 := by
    simpa [prefixWord, tailWord_3030805, baseEnd_3030805] using wordTrace_append hprefix tailTrace_3030805
  have hstable : (prefixWord ++ tailWord_3030805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030805).length < 2 ^ (prefixWord ++ tailWord_3030805).sum := by decide
  have hdescent : baseEnd_3030805 < baseStart_3030805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030820 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3030820 : Nat := 118140960795 + 3030820 * 2 ^ 59
def prefixEnd_3030820 : Nat := 4983230072969 + 3 ^ 40 * 3030820 * 2
def baseEnd_3030820 : Nat := 345837208279986030335893

theorem tailTrace_3030820 : CollatzResearch.WordTrace tailWord_3030820 prefixEnd_3030820 345837208279986030335893 := by
  unfold tailWord_3030820
  simp only [CollatzResearch.WordTrace]
  refine ⟨55271543439932118845524957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73695391253242825127366609 55271543439932118845524957)
  ·
    refine ⟨20726828789974544567071859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55271543439932118845524957 20726828789974544567071859)
    ·
      refine ⟨31090243184961816850607789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20726828789974544567071859 31090243184961816850607789)
      ·
        refine ⟨11658841194360681318977921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31090243184961816850607789 11658841194360681318977921)
        ·
          refine ⟨8744130895770510989233441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11658841194360681318977921 8744130895770510989233441)
          ·
            refine ⟨6558098171827883241925081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8744130895770510989233441 6558098171827883241925081)
            ·
              refine ⟨4918573628870912431443811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6558098171827883241925081 4918573628870912431443811)
              ·
                refine ⟨7377860443306368647165717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918573628870912431443811 7377860443306368647165717)
                ·
                  refine ⟨345837208279986030335893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7377860443306368647165717 345837208279986030335893)
                  ·
                    rfl

theorem cell22_3030820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3030820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030820 prefixEnd_3030820 := by exact prefixLift 3030820
  have htrace : WordTrace (prefixWord ++ tailWord_3030820) baseStart_3030820 baseEnd_3030820 := by
    simpa [prefixWord, tailWord_3030820, baseEnd_3030820] using wordTrace_append hprefix tailTrace_3030820
  have hstable : (prefixWord ++ tailWord_3030820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030820).length < 2 ^ (prefixWord ++ tailWord_3030820).sum := by decide
  have hdescent : baseEnd_3030820 < baseStart_3030820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030833 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3030833 : Nat := 118140960795 + 3030833 * 2 ^ 59
def prefixEnd_3030833 : Nat := 4983230072969 + 3 ^ 40 * 3030833 * 2
def baseEnd_3030833 : Nat := 1037516075005630390432639

theorem tailTrace_3030833 : CollatzResearch.WordTrace tailWord_3030833 prefixEnd_3030833 1037516075005630390432639 := by
  unfold tailWord_3030833
  simp only [CollatzResearch.WordTrace]
  refine ⟨110543561028817140911273153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73695707352544760607515435 110543561028817140911273153)
  ·
    refine ⟨82907670771612855683454865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110543561028817140911273153 82907670771612855683454865)
    ·
      refine ⟨62180753078709641762591149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82907670771612855683454865 62180753078709641762591149)
      ·
        refine ⟨23317782404516115660971681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62180753078709641762591149 23317782404516115660971681)
        ·
          refine ⟨17488336803387086745728761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23317782404516115660971681 17488336803387086745728761)
          ·
            refine ⟨13116252602540315059296571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17488336803387086745728761 13116252602540315059296571)
            ·
              refine ⟨19674378903810472588944857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13116252602540315059296571 19674378903810472588944857)
              ·
                refine ⟨14755784177857854441708643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19674378903810472588944857 14755784177857854441708643)
                ·
                  refine ⟨22133676266786781662562965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14755784177857854441708643 22133676266786781662562965)
                  ·
                    refine ⟨1037516075005630390432639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22133676266786781662562965 1037516075005630390432639)
                    ·
                      rfl

theorem cell22_3030833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3030833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030833 prefixEnd_3030833 := by exact prefixLift 3030833
  have htrace : WordTrace (prefixWord ++ tailWord_3030833) baseStart_3030833 baseEnd_3030833 := by
    simpa [prefixWord, tailWord_3030833, baseEnd_3030833] using wordTrace_append hprefix tailTrace_3030833
  have hstable : (prefixWord ++ tailWord_3030833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030833).length < 2 ^ (prefixWord ++ tailWord_3030833).sum := by decide
  have hdescent : baseEnd_3030833 < baseStart_3030833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030908 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3030908 : Nat := 118140960795 + 3030908 * 2 ^ 59
def prefixEnd_3030908 : Nat := 4983230072969 + 3 ^ 40 * 3030908 * 2
def baseEnd_3030908 : Nat := 1037541749038355194807409

theorem tailTrace_3030908 : CollatzResearch.WordTrace tailWord_3030908 prefixEnd_3030908 1037541749038355194807409 := by
  unfold tailWord_3030908
  simp only [CollatzResearch.WordTrace]
  refine ⟨55273148251772714360126689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73697531002363619146835585 55273148251772714360126689)
  ·
    refine ⟨41454861188829535770095017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55273148251772714360126689 41454861188829535770095017)
    ·
      refine ⟨31091145891622151827571263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41454861188829535770095017 31091145891622151827571263)
      ·
        refine ⟨46636718837433227741356895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31091145891622151827571263 46636718837433227741356895)
        ·
          refine ⟨69955078256149841612035343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46636718837433227741356895 69955078256149841612035343)
          ·
            refine ⟨104932617384224762418053015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69955078256149841612035343 104932617384224762418053015)
            ·
              refine ⟨157398926076337143627079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104932617384224762418053015 157398926076337143627079523)
              ·
                refine ⟨236098389114505715440619285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157398926076337143627079523 236098389114505715440619285)
                ·
                  refine ⟨11067111989742455411279029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236098389114505715440619285 11067111989742455411279029)
                  ·
                    refine ⟨1037541749038355194807409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11067111989742455411279029 1037541749038355194807409)
                    ·
                      rfl

theorem cell22_3030908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3030908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030908 prefixEnd_3030908 := by exact prefixLift 3030908
  have htrace : WordTrace (prefixWord ++ tailWord_3030908) baseStart_3030908 baseEnd_3030908 := by
    simpa [prefixWord, tailWord_3030908, baseEnd_3030908] using wordTrace_append hprefix tailTrace_3030908
  have hstable : (prefixWord ++ tailWord_3030908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030908).length < 2 ^ (prefixWord ++ tailWord_3030908).sum := by decide
  have hdescent : baseEnd_3030908 < baseStart_3030908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030974 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3030974 : Nat := 118140960795 + 3030974 * 2 ^ 59
def prefixEnd_3030974 : Nat := 4983230072969 + 3 ^ 40 * 3030974 * 2
def baseEnd_3030974 : Nat := 1037564342187153022657207

theorem tailTrace_3030974 : CollatzResearch.WordTrace tailWord_3030974 prefixEnd_3030974 1037564342187153022657207 := by
  unfold tailWord_3030974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13818587965163290249019497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73699135814204214661437317 13818587965163290249019497)
  ·
    refine ⟨10363940973872467686764623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13818587965163290249019497 10363940973872467686764623)
    ·
      refine ⟨15545911460808701530146935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10363940973872467686764623 15545911460808701530146935)
      ·
        refine ⟨23318867191213052295220403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15545911460808701530146935 23318867191213052295220403)
        ·
          refine ⟨34978300786819578442830605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23318867191213052295220403 34978300786819578442830605)
          ·
            refine ⟨13116862795057341916061477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34978300786819578442830605 13116862795057341916061477)
            ·
              refine ⟨2459411774073251609261527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13116862795057341916061477 2459411774073251609261527)
              ·
                refine ⟨3689117661109877413892291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459411774073251609261527 3689117661109877413892291)
                ·
                  refine ⟨5533676491664816120838437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689117661109877413892291 5533676491664816120838437)
                  ·
                    refine ⟨1037564342187153022657207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533676491664816120838437 1037564342187153022657207)
                    ·
                      rfl

theorem cell22_3030974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3030974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3030974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3030974 prefixEnd_3030974 := by exact prefixLift 3030974
  have htrace : WordTrace (prefixWord ++ tailWord_3030974) baseStart_3030974 baseEnd_3030974 := by
    simpa [prefixWord, tailWord_3030974, baseEnd_3030974] using wordTrace_append hprefix tailTrace_3030974
  have hstable : (prefixWord ++ tailWord_3030974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030974).length < 2 ^ (prefixWord ++ tailWord_3030974).sum := by decide
  have hdescent : baseEnd_3030974 < baseStart_3030974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031045 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 7]
def baseStart_3031045 : Nat := 118140960795 + 3031045 * 2 ^ 59
def prefixEnd_3031045 : Nat := 4983230072969 + 3 ^ 40 * 3031045 * 2
def baseEnd_3031045 : Nat := 345862882312710834710663

theorem tailTrace_3031045 : CollatzResearch.WordTrace tailWord_3031045 prefixEnd_3031045 345862882312710834710663 := by
  unfold tailWord_3031045
  simp only [CollatzResearch.WordTrace]
  refine ⟨110551293304049101117990589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73700862202699400745327059 110551293304049101117990589)
  ·
    refine ⟨41456734989018412919246471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110551293304049101117990589 41456734989018412919246471)
    ·
      refine ⟨62185102483527619378869707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41456734989018412919246471 62185102483527619378869707)
      ·
        refine ⟨93277653725291429068304561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62185102483527619378869707 93277653725291429068304561)
        ·
          refine ⟨69958240293968571801228421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93277653725291429068304561 69958240293968571801228421)
          ·
            refine ⟨13117170055119107212730329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69958240293968571801228421 13117170055119107212730329)
            ·
              refine ⟨9837877541339330409547747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13117170055119107212730329 9837877541339330409547747)
              ·
                refine ⟨14756816312008995614321621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837877541339330409547747 14756816312008995614321621)
                ·
                  refine ⟨345862882312710834710663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14756816312008995614321621 345862882312710834710663)
                  ·
                    rfl

theorem cell22_3031045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_3031045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031045 prefixEnd_3031045 := by exact prefixLift 3031045
  have htrace : WordTrace (prefixWord ++ tailWord_3031045) baseStart_3031045 baseEnd_3031045 := by
    simpa [prefixWord, tailWord_3031045, baseEnd_3031045] using wordTrace_append hprefix tailTrace_3031045
  have hstable : (prefixWord ++ tailWord_3031045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031045).length < 2 ^ (prefixWord ++ tailWord_3031045).sum := by decide
  have hdescent : baseEnd_3031045 < baseStart_3031045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031126 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3031126 : Nat := 118140960795 + 3031126 * 2 ^ 59
def prefixEnd_3031126 : Nat := 4983230072969 + 3 ^ 40 * 3031126 * 2
def baseEnd_3031126 : Nat := 1037616374893475292856741

theorem tailTrace_3031126 : CollatzResearch.WordTrace tailWord_3031126 prefixEnd_3031126 1037616374893475292856741 := by
  unfold tailWord_3031126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909640476047228246980577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73702831744503767967792821 6909640476047228246980577)
  ·
    refine ⟨5182230357035421185235433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6909640476047228246980577 5182230357035421185235433)
    ·
      refine ⟨3886672767776565888926575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5182230357035421185235433 3886672767776565888926575)
      ·
        refine ⟨5830009151664848833389863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886672767776565888926575 5830009151664848833389863)
        ·
          refine ⟨8745013727497273250084795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5830009151664848833389863 8745013727497273250084795)
          ·
            refine ⟨13117520591245909875127193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745013727497273250084795 13117520591245909875127193)
            ·
              refine ⟨9838140443434432406345395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13117520591245909875127193 9838140443434432406345395)
              ·
                refine ⟨14757210665151648609518093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9838140443434432406345395 14757210665151648609518093)
                ·
                  refine ⟨5533953999431868228569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14757210665151648609518093 5533953999431868228569285)
                  ·
                    refine ⟨1037616374893475292856741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533953999431868228569285 1037616374893475292856741)
                    ·
                      rfl

theorem cell22_3031126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3031126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031126 prefixEnd_3031126 := by exact prefixLift 3031126
  have htrace : WordTrace (prefixWord ++ tailWord_3031126) baseStart_3031126 baseEnd_3031126 := by
    simpa [prefixWord, tailWord_3031126, baseEnd_3031126] using wordTrace_append hprefix tailTrace_3031126
  have hstable : (prefixWord ++ tailWord_3031126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031126).length < 2 ^ (prefixWord ++ tailWord_3031126).sum := by decide
  have hdescent : baseEnd_3031126 < baseStart_3031126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031197 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3031197 : Nat := 118140960795 + 3031197 * 2 ^ 59
def prefixEnd_3031197 : Nat := 4983230072969 + 3 ^ 40 * 3031197 * 2
def baseEnd_3031197 : Nat := 345880226548151591443841

theorem tailTrace_3031197 : CollatzResearch.WordTrace tailWord_3031197 prefixEnd_3031197 345880226548151591443841 := by
  unfold tailWord_3031197
  simp only [CollatzResearch.WordTrace]
  refine ⟨110556837199498431077523845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73704558132998954051682563 110556837199498431077523845)
  ·
    refine ⟨20729406974905955827035721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110556837199498431077523845 20729406974905955827035721)
    ·
      refine ⟨15547055231179466870276791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20729406974905955827035721 15547055231179466870276791)
      ·
        refine ⟨23320582846769200305415187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15547055231179466870276791 23320582846769200305415187)
        ·
          refine ⟨34980874270153800458122781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23320582846769200305415187 34980874270153800458122781)
          ·
            refine ⟨13117827851307675171796043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34980874270153800458122781 13117827851307675171796043)
            ·
              refine ⟨19676741776961512757694065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13117827851307675171796043 19676741776961512757694065)
              ·
                refine ⟨14757556332721134568270549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19676741776961512757694065 14757556332721134568270549)
                ·
                  refine ⟨345880226548151591443841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14757556332721134568270549 345880226548151591443841)
                  ·
                    rfl

theorem cell22_3031197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3031197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031197 prefixEnd_3031197 := by exact prefixLift 3031197
  have htrace : WordTrace (prefixWord ++ tailWord_3031197) baseStart_3031197 baseEnd_3031197 := by
    simpa [prefixWord, tailWord_3031197, baseEnd_3031197] using wordTrace_append hprefix tailTrace_3031197
  have hstable : (prefixWord ++ tailWord_3031197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031197).length < 2 ^ (prefixWord ++ tailWord_3031197).sum := by decide
  have hdescent : baseEnd_3031197 < baseStart_3031197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031218 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_3031218 : Nat := 118140960795 + 3031218 * 2 ^ 59
def prefixEnd_3031218 : Nat := 4983230072969 + 3 ^ 40 * 3031218 * 2
def baseEnd_3031218 : Nat := 1037647868373617719556459

theorem tailTrace_3031218 : CollatzResearch.WordTrace tailWord_3031218 prefixEnd_3031218 1037647868373617719556459 := by
  unfold tailWord_3031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639400783105587916009577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73705068754948234442692205 27639400783105587916009577)
  ·
    refine ⟨20729550587329190937007183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27639400783105587916009577 20729550587329190937007183)
    ·
      refine ⟨31094325880993786405510775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20729550587329190937007183 31094325880993786405510775)
      ·
        refine ⟨46641488821490679608266163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31094325880993786405510775 46641488821490679608266163)
        ·
          refine ⟨69962233232236019412399245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46641488821490679608266163 69962233232236019412399245)
          ·
            refine ⟨26235837462088507279649717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69962233232236019412399245 26235837462088507279649717)
            ·
              refine ⟨2459609762070797557467161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26235837462088507279649717 2459609762070797557467161)
              ·
                refine ⟨1844707321553098168100371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459609762070797557467161 1844707321553098168100371)
                ·
                  refine ⟨2767060982329647252150557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844707321553098168100371 2767060982329647252150557)
                  ·
                    refine ⟨1037647868373617719556459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767060982329647252150557 1037647868373617719556459)
                    ·
                      rfl

theorem cell22_3031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_3031218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031218 prefixEnd_3031218 := by exact prefixLift 3031218
  have htrace : WordTrace (prefixWord ++ tailWord_3031218) baseStart_3031218 baseEnd_3031218 := by
    simpa [prefixWord, tailWord_3031218, baseEnd_3031218] using wordTrace_append hprefix tailTrace_3031218
  have hstable : (prefixWord ++ tailWord_3031218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031218).length < 2 ^ (prefixWord ++ tailWord_3031218).sum := by decide
  have hdescent : baseEnd_3031218 < baseStart_3031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031227 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_3031227 : Nat := 118140960795 + 3031227 * 2 ^ 59
def prefixEnd_3031227 : Nat := 4983230072969 + 3 ^ 40 * 3031227 * 2
def baseEnd_3031227 : Nat := 1037650949257544696081431

theorem tailTrace_3031227 : CollatzResearch.WordTrace tailWord_3031227 prefixEnd_3031227 1037650949257544696081431 := by
  unfold tailWord_3031227
  simp only [CollatzResearch.WordTrace]
  refine ⟨110557931389389746201115935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73705287592926497467410623 110557931389389746201115935)
  ·
    refine ⟨165836897084084619301673903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110557931389389746201115935 165836897084084619301673903)
    ·
      refine ⟨248755345626126928952510855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165836897084084619301673903 248755345626126928952510855)
      ·
        refine ⟨373133018439190393428766283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248755345626126928952510855 373133018439190393428766283)
        ·
          refine ⟨559699527658785590143149425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373133018439190393428766283 559699527658785590143149425)
          ·
            refine ⟨419774645744089192607362069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559699527658785590143149425 419774645744089192607362069)
            ·
              refine ⟨19676936519254180903470097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 419774645744089192607362069 19676936519254180903470097)
              ·
                refine ⟨14757702389440635677602573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19676936519254180903470097 14757702389440635677602573)
                ·
                  refine ⟨5534138396040238379100965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14757702389440635677602573 5534138396040238379100965)
                  ·
                    refine ⟨1037650949257544696081431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5534138396040238379100965 1037650949257544696081431)
                    ·
                      rfl

theorem cell22_3031227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_3031227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031227 prefixEnd_3031227 := by exact prefixLift 3031227
  have htrace : WordTrace (prefixWord ++ tailWord_3031227) baseStart_3031227 baseEnd_3031227 := by
    simpa [prefixWord, tailWord_3031227, baseEnd_3031227] using wordTrace_append hprefix tailTrace_3031227
  have hstable : (prefixWord ++ tailWord_3031227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031227).length < 2 ^ (prefixWord ++ tailWord_3031227).sum := by decide
  have hdescent : baseEnd_3031227 < baseStart_3031227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031242 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_3031242 : Nat := 118140960795 + 3031242 * 2 ^ 59
def prefixEnd_3031242 : Nat := 4983230072969 + 3 ^ 40 * 3031242 * 2
def baseEnd_3031242 : Nat := 345885361354696552318795

theorem tailTrace_3031242 : CollatzResearch.WordTrace tailWord_3031242 prefixEnd_3031242 345885361354696552318795 := by
  unfold tailWord_3031242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639619621083850940727995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73705652322890269175274653 27639619621083850940727995)
  ·
    refine ⟨41459429431625776411091993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27639619621083850940727995 41459429431625776411091993)
    ·
      refine ⟨31094572073719332308318995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41459429431625776411091993 31094572073719332308318995)
      ·
        refine ⟨46641858110578998462478493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31094572073719332308318995 46641858110578998462478493)
        ·
          refine ⟨17490696791467124423429435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46641858110578998462478493 17490696791467124423429435)
          ·
            refine ⟨26236045187200686635144153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17490696791467124423429435 26236045187200686635144153)
            ·
              refine ⟨19677033890400514976358115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26236045187200686635144153 19677033890400514976358115)
              ·
                refine ⟨29515550835600772464537173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19677033890400514976358115 29515550835600772464537173)
                ·
                  refine ⟨345885361354696552318795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29515550835600772464537173 345885361354696552318795)
                  ·
                    rfl

theorem cell22_3031242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_3031242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031242 prefixEnd_3031242 := by exact prefixLift 3031242
  have htrace : WordTrace (prefixWord ++ tailWord_3031242) baseStart_3031242 baseEnd_3031242 := by
    simpa [prefixWord, tailWord_3031242, baseEnd_3031242] using wordTrace_append hprefix tailTrace_3031242
  have hstable : (prefixWord ++ tailWord_3031242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031242).length < 2 ^ (prefixWord ++ tailWord_3031242).sum := by decide
  have hdescent : baseEnd_3031242 < baseStart_3031242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031257 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3031257 : Nat := 118140960795 + 3031257 * 2 ^ 59
def prefixEnd_3031257 : Nat := 4983230072969 + 3 ^ 40 * 3031257 * 2
def baseEnd_3031257 : Nat := 1037661218870634617831339

theorem tailTrace_3031257 : CollatzResearch.WordTrace tailWord_3031257 prefixEnd_3031257 1037661218870634617831339 := by
  unfold tailWord_3031257
  simp only [CollatzResearch.WordTrace]
  refine ⟨110559025579281061324708025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73706017052854040883138683 110559025579281061324708025)
  ·
    refine ⟨82919269184460795993531019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110559025579281061324708025 82919269184460795993531019)
    ·
      refine ⟨124378903776691193990296529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82919269184460795993531019 124378903776691193990296529)
      ·
        refine ⟨93284177832518395492722397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124378903776691193990296529 93284177832518395492722397)
        ·
          refine ⟨34981566687194398309770899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93284177832518395492722397 34981566687194398309770899)
          ·
            refine ⟨52472350030791597464656349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34981566687194398309770899 52472350030791597464656349)
            ·
              refine ⟨19677131261546849049246131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52472350030791597464656349 19677131261546849049246131)
              ·
                refine ⟨29515696892320273573869197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19677131261546849049246131 29515696892320273573869197)
                ·
                  refine ⟨11068386334620102590200949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29515696892320273573869197 11068386334620102590200949)
                  ·
                    refine ⟨1037661218870634617831339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11068386334620102590200949 1037661218870634617831339)
                    ·
                      rfl

theorem cell22_3031257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3031257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031257 prefixEnd_3031257 := by exact prefixLift 3031257
  have htrace : WordTrace (prefixWord ++ tailWord_3031257) baseStart_3031257 baseEnd_3031257 := by
    simpa [prefixWord, tailWord_3031257, baseEnd_3031257] using wordTrace_append hprefix tailTrace_3031257
  have hstable : (prefixWord ++ tailWord_3031257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031257).length < 2 ^ (prefixWord ++ tailWord_3031257).sum := by decide
  have hdescent : baseEnd_3031257 < baseStart_3031257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031325 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3031325 : Nat := 118140960795 + 3031325 * 2 ^ 59
def prefixEnd_3031325 : Nat := 4983230072969 + 3 ^ 40 * 3031325 * 2
def baseEnd_3031325 : Nat := 1037684496660305107131131

theorem tailTrace_3031325 : CollatzResearch.WordTrace tailWord_3031325 prefixEnd_3031325 1037684496660305107131131 := by
  unfold tailWord_3031325
  simp only [CollatzResearch.WordTrace]
  refine ⟨110561505743034708938183429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73707670495356472625455619 110561505743034708938183429)
  ·
    refine ⟨20730282326819007925909393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110561505743034708938183429 20730282326819007925909393)
    ·
      refine ⟨15547711745114255944432045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20730282326819007925909393 15547711745114255944432045)
      ·
        refine ⟨5830391904417845979162017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15547711745114255944432045 5830391904417845979162017)
        ·
          refine ⟨4372793928313384484371513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830391904417845979162017 4372793928313384484371513)
          ·
            refine ⟨3279595446235038363278635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4372793928313384484371513 3279595446235038363278635)
            ·
              refine ⟨4919393169352557544917953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279595446235038363278635 4919393169352557544917953)
              ·
                refine ⟨3689544877014418158688465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919393169352557544917953 3689544877014418158688465)
                ·
                  refine ⟨2767158657760813619016349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3689544877014418158688465 2767158657760813619016349)
                  ·
                    refine ⟨1037684496660305107131131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767158657760813619016349 1037684496660305107131131)
                    ·
                      rfl

theorem cell22_3031325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3031325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031325 prefixEnd_3031325 := by exact prefixLift 3031325
  have htrace : WordTrace (prefixWord ++ tailWord_3031325) baseStart_3031325 baseEnd_3031325 := by
    simpa [prefixWord, tailWord_3031325, baseEnd_3031325] using wordTrace_append hprefix tailTrace_3031325
  have hstable : (prefixWord ++ tailWord_3031325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031325).length < 2 ^ (prefixWord ++ tailWord_3031325).sum := by decide
  have hdescent : baseEnd_3031325 < baseStart_3031325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031342 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3031342 : Nat := 118140960795 + 3031342 * 2 ^ 59
def prefixEnd_3031342 : Nat := 4983230072969 + 3 ^ 40 * 3031342 * 2
def baseEnd_3031342 : Nat := 1037690316107722729456079

theorem tailTrace_3031342 : CollatzResearch.WordTrace tailWord_3031342 prefixEnd_3031342 1037690316107722729456079 := by
  unfold tailWord_3031342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820265722996640105194035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73708083855982080561034853 13820265722996640105194035)
  ·
    refine ⟨20730398584494960157791053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13820265722996640105194035 20730398584494960157791053)
    ·
      refine ⟨7773899469185610059171645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20730398584494960157791053 7773899469185610059171645)
      ·
        refine ⟨2915212300944603772189367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7773899469185610059171645 2915212300944603772189367)
        ·
          refine ⟨4372818451416905658284051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915212300944603772189367 4372818451416905658284051)
          ·
            refine ⟨6559227677125358487426077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372818451416905658284051 6559227677125358487426077)
            ·
              refine ⟨2459710378922009432784779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6559227677125358487426077 2459710378922009432784779)
              ·
                refine ⟨3689565568383014149177169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459710378922009432784779 3689565568383014149177169)
                ·
                  refine ⟨2767174176287260611882877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3689565568383014149177169 2767174176287260611882877)
                  ·
                    refine ⟨1037690316107722729456079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767174176287260611882877 1037690316107722729456079)
                    ·
                      rfl

theorem cell22_3031342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3031342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031342 prefixEnd_3031342 := by exact prefixLift 3031342
  have htrace : WordTrace (prefixWord ++ tailWord_3031342) baseStart_3031342 baseEnd_3031342 := by
    simpa [prefixWord, tailWord_3031342, baseEnd_3031342] using wordTrace_append hprefix tailTrace_3031342
  have hstable : (prefixWord ++ tailWord_3031342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031342).length < 2 ^ (prefixWord ++ tailWord_3031342).sum := by decide
  have hdescent : baseEnd_3031342 < baseStart_3031342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031409 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3031409 : Nat := 118140960795 + 3031409 * 2 ^ 59
def prefixEnd_3031409 : Nat := 4983230072969 + 3 ^ 40 * 3031409 * 2
def baseEnd_3031409 : Nat := 1037713251576956888030873

theorem tailTrace_3031409 : CollatzResearch.WordTrace tailWord_3031409 prefixEnd_3031409 1037713251576956888030873 := by
  unfold tailWord_3031409
  simp only [CollatzResearch.WordTrace]
  refine ⟨110564569474730391284241281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73709712983153594189494187 110564569474730391284241281)
  ·
    refine ⟨82923427106047793463180961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110564569474730391284241281 82923427106047793463180961)
    ·
      refine ⟨62192570329535845097385721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82923427106047793463180961 62192570329535845097385721)
      ·
        refine ⟨46644427747151883823039291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62192570329535845097385721 46644427747151883823039291)
        ·
          refine ⟨69966641620727825734558937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46644427747151883823039291 69966641620727825734558937)
          ·
            refine ⟨52474981215545869300919203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69966641620727825734558937 52474981215545869300919203)
            ·
              refine ⟨78712471823318803951378805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52474981215545869300919203 78712471823318803951378805)
              ·
                refine ⟨7379294233436137870441763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78712471823318803951378805 7379294233436137870441763)
                ·
                  refine ⟨11068941350154206805662645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379294233436137870441763 11068941350154206805662645)
                  ·
                    refine ⟨1037713251576956888030873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11068941350154206805662645 1037713251576956888030873)
                    ·
                      rfl

theorem cell22_3031409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3031409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031409 prefixEnd_3031409 := by exact prefixLift 3031409
  have htrace : WordTrace (prefixWord ++ tailWord_3031409) baseStart_3031409 baseEnd_3031409 := by
    simpa [prefixWord, tailWord_3031409, baseEnd_3031409] using wordTrace_append hprefix tailTrace_3031409
  have hstable : (prefixWord ++ tailWord_3031409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031409).length < 2 ^ (prefixWord ++ tailWord_3031409).sum := by decide
  have hdescent : baseEnd_3031409 < baseStart_3031409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031413 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3031413 : Nat := 118140960795 + 3031413 * 2 ^ 59
def prefixEnd_3031413 : Nat := 4983230072969 + 3 ^ 40 * 3031413 * 2
def baseEnd_3031413 : Nat := 1037714620858702210930861

theorem tailTrace_3031413 : CollatzResearch.WordTrace tailWord_3031413 prefixEnd_3031413 1037714620858702210930861 := by
  unfold tailWord_3031413
  simp only [CollatzResearch.WordTrace]
  refine ⟨110564715366715899967386893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73709810244477266644924595 110564715366715899967386893)
  ·
    refine ⟨41461768262518462487770085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110564715366715899967386893 41461768262518462487770085)
    ·
      refine ⟨7774081549222211716456891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41461768262518462487770085 7774081549222211716456891)
      ·
        refine ⟨11661122323833317574685337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774081549222211716456891 11661122323833317574685337)
        ·
          refine ⟨8745841742874988181014003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11661122323833317574685337 8745841742874988181014003)
          ·
            refine ⟨13118762614312482271521005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745841742874988181014003 13118762614312482271521005)
            ·
              refine ⟨4919535980367180851820377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13118762614312482271521005 4919535980367180851820377)
              ·
                refine ⟨3689651985275385638865283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919535980367180851820377 3689651985275385638865283)
                ·
                  refine ⟨5534477977913078458297925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689651985275385638865283 5534477977913078458297925)
                  ·
                    refine ⟨1037714620858702210930861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5534477977913078458297925 1037714620858702210930861)
                    ·
                      rfl

theorem cell22_3031413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3031413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031413 prefixEnd_3031413 := by exact prefixLift 3031413
  have htrace : WordTrace (prefixWord ++ tailWord_3031413) baseStart_3031413 baseEnd_3031413 := by
    simpa [prefixWord, tailWord_3031413, baseEnd_3031413] using wordTrace_append hprefix tailTrace_3031413
  have hstable : (prefixWord ++ tailWord_3031413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031413).length < 2 ^ (prefixWord ++ tailWord_3031413).sum := by decide
  have hdescent : baseEnd_3031413 < baseStart_3031413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031456 : List Nat := [2, 1, 1, 4, 1, 5, 1, 7]
def baseStart_3031456 : Nat := 118140960795 + 3031456 * 2 ^ 59
def prefixEnd_3031456 : Nat := 4983230072969 + 3 ^ 40 * 3031456 * 2
def baseEnd_3031456 : Nat := 115303260070829381345081

theorem tailTrace_3031456 : CollatzResearch.WordTrace tailWord_3031456 prefixEnd_3031456 115303260070829381345081 := by
  unfold tailWord_3031456
  simp only [CollatzResearch.WordTrace]
  refine ⟨55283141852780059155601111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73710855803706745540801481 55283141852780059155601111)
  ·
    refine ⟨82924712779170088733401667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55283141852780059155601111 82924712779170088733401667)
    ·
      refine ⟨124387069168755133100102501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82924712779170088733401667 124387069168755133100102501)
      ·
        refine ⟨23322575469141587456269219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124387069168755133100102501 23322575469141587456269219)
        ·
          refine ⟨34983863203712381184403829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23322575469141587456269219 34983863203712381184403829)
          ·
            refine ⟨3279737175348035736037859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34983863203712381184403829 3279737175348035736037859)
            ·
              refine ⟨4919605763022053604056789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279737175348035736037859 4919605763022053604056789)
              ·
                refine ⟨115303260070829381345081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4919605763022053604056789 115303260070829381345081)
                ·
                  rfl

theorem cell22_3031456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_3031456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031456 prefixEnd_3031456 := by exact prefixLift 3031456
  have htrace : WordTrace (prefixWord ++ tailWord_3031456) baseStart_3031456 baseEnd_3031456 := by
    simpa [prefixWord, tailWord_3031456, baseEnd_3031456] using wordTrace_append hprefix tailTrace_3031456
  have hstable : (prefixWord ++ tailWord_3031456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031456).length < 2 ^ (prefixWord ++ tailWord_3031456).sum := by decide
  have hdescent : baseEnd_3031456 < baseStart_3031456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031529 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 8]
def baseStart_3031529 : Nat := 118140960795 + 3031529 * 2 ^ 59
def prefixEnd_3031529 : Nat := 4983230072969 + 3 ^ 40 * 3031529 * 2
def baseEnd_3031529 : Nat := 345918110009772191676835

theorem tailTrace_3031529 : CollatzResearch.WordTrace tailWord_3031529 prefixEnd_3031529 345918110009772191676835 := by
  unfold tailWord_3031529
  simp only [CollatzResearch.WordTrace]
  refine ⟨110568946234295651778609641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73712630822863767852406427 110568946234295651778609641)
  ·
    refine ⟨82926709675721738833957231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110568946234295651778609641 82926709675721738833957231)
    ·
      refine ⟨124390064513582608250935847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82926709675721738833957231 124390064513582608250935847)
      ·
        refine ⟨186585096770373912376403771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124390064513582608250935847 186585096770373912376403771)
        ·
          refine ⟨279877645155560868564605657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186585096770373912376403771 279877645155560868564605657)
          ·
            refine ⟨209908233866670651423454243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279877645155560868564605657 209908233866670651423454243)
            ·
              refine ⟨314862350800005977135181365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209908233866670651423454243 314862350800005977135181365)
              ·
                refine ⟨29518345387500560356423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314862350800005977135181365 29518345387500560356423253)
                ·
                  refine ⟨345918110009772191676835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29518345387500560356423253 345918110009772191676835)
                  ·
                    rfl

theorem cell22_3031529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_3031529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031529 prefixEnd_3031529 := by exact prefixLift 3031529
  have htrace : WordTrace (prefixWord ++ tailWord_3031529) baseStart_3031529 baseEnd_3031529 := by
    simpa [prefixWord, tailWord_3031529, baseEnd_3031529] using wordTrace_append hprefix tailTrace_3031529
  have hstable : (prefixWord ++ tailWord_3031529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031529).length < 2 ^ (prefixWord ++ tailWord_3031529).sum := by decide
  have hdescent : baseEnd_3031529 < baseStart_3031529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031563 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 6]
def baseStart_3031563 : Nat := 118140960795 + 3031563 * 2 ^ 59
def prefixEnd_3031563 : Nat := 4983230072969 + 3 ^ 40 * 3031563 * 2
def baseEnd_3031563 : Nat := 345921989641383939893467

theorem tailTrace_3031563 : CollatzResearch.WordTrace tailWord_3031563 prefixEnd_3031563 345921989641383939893467 := by
  unfold tailWord_3031563
  simp only [CollatzResearch.WordTrace]
  refine ⟨110570186316172475585347343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73713457544114983723564895 110570186316172475585347343)
  ·
    refine ⟨165855279474258713378021015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110570186316172475585347343 165855279474258713378021015)
    ·
      refine ⟨248782919211388070067031523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165855279474258713378021015 248782919211388070067031523)
      ·
        refine ⟨373174378817082105100547285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248782919211388070067031523 373174378817082105100547285)
        ·
          refine ⟨8746274503525361838294077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 373174378817082105100547285 8746274503525361838294077)
          ·
            refine ⟨3279852938822010689360279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8746274503525361838294077 3279852938822010689360279)
            ·
              refine ⟨4919779408233016034040419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279852938822010689360279 4919779408233016034040419)
              ·
                refine ⟨7379669112349524051060629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919779408233016034040419 7379669112349524051060629)
                ·
                  refine ⟨345921989641383939893467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7379669112349524051060629 345921989641383939893467)
                  ·
                    rfl

theorem cell22_3031563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].length) (baseStart_3031563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031563 prefixEnd_3031563 := by exact prefixLift 3031563
  have htrace : WordTrace (prefixWord ++ tailWord_3031563) baseStart_3031563 baseEnd_3031563 := by
    simpa [prefixWord, tailWord_3031563, baseEnd_3031563] using wordTrace_append hprefix tailTrace_3031563
  have hstable : (prefixWord ++ tailWord_3031563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031563).length < 2 ^ (prefixWord ++ tailWord_3031563).sum := by decide
  have hdescent : baseEnd_3031563 < baseStart_3031563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031621 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_3031621 : Nat := 118140960795 + 3031621 * 2 ^ 59
def prefixEnd_3031621 : Nat := 4983230072969 + 3 ^ 40 * 3031621 * 2
def baseEnd_3031621 : Nat := 1037785823509459001730223

theorem tailTrace_3031621 : CollatzResearch.WordTrace tailWord_3031621 prefixEnd_3031621 1037785823509459001730223 := by
  unfold tailWord_3031621
  simp only [CollatzResearch.WordTrace]
  refine ⟨110572301749962351490958717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73714867833308234327305811 110572301749962351490958717)
  ·
    refine ⟨41464613156235881809109519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110572301749962351490958717 41464613156235881809109519)
    ·
      refine ⟨62196919734353822713664279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41464613156235881809109519 62196919734353822713664279)
      ·
        refine ⟨93295379601530734070496419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62196919734353822713664279 93295379601530734070496419)
        ·
          refine ⟨139943069402296101105744629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93295379601530734070496419 139943069402296101105744629)
          ·
            refine ⟨13119662756465259478663559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139943069402296101105744629 13119662756465259478663559)
            ·
              refine ⟨19679494134697889217995339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13119662756465259478663559 19679494134697889217995339)
              ·
                refine ⟨29519241202046833826993009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19679494134697889217995339 29519241202046833826993009)
                ·
                  refine ⟨22139430901535125370244757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29519241202046833826993009 22139430901535125370244757)
                  ·
                    refine ⟨1037785823509459001730223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22139430901535125370244757 1037785823509459001730223)
                    ·
                      rfl

theorem cell22_3031621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_3031621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031621 prefixEnd_3031621 := by exact prefixLift 3031621
  have htrace : WordTrace (prefixWord ++ tailWord_3031621) baseStart_3031621 baseEnd_3031621 := by
    simpa [prefixWord, tailWord_3031621, baseEnd_3031621] using wordTrace_append hprefix tailTrace_3031621
  have hstable : (prefixWord ++ tailWord_3031621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031621).length < 2 ^ (prefixWord ++ tailWord_3031621).sum := by decide
  have hdescent : baseEnd_3031621 < baseStart_3031621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031651 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_3031651 : Nat := 118140960795 + 3031651 * 2 ^ 59
def prefixEnd_3031651 : Nat := 4983230072969 + 3 ^ 40 * 3031651 * 2
def baseEnd_3031651 : Nat := 1037796093122548923480131

theorem tailTrace_3031651 : CollatzResearch.WordTrace tailWord_3031651 prefixEnd_3031651 1037796093122548923480131 := by
  unfold tailWord_3031651
  simp only [CollatzResearch.WordTrace]
  refine ⟨110573395939853666614550807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73715597293235777743033871 110573395939853666614550807)
  ·
    refine ⟨165860093909780499921826211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110573395939853666614550807 165860093909780499921826211)
    ·
      refine ⟨248790140864670749882739317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165860093909780499921826211 248790140864670749882739317)
      ·
        refine ⟨23324075706062882801506811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248790140864670749882739317 23324075706062882801506811)
        ·
          refine ⟨34986113559094324202260217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23324075706062882801506811 34986113559094324202260217)
          ·
            refine ⟨26239585169320743151695163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34986113559094324202260217 26239585169320743151695163)
            ·
              refine ⟨39359377753981114727542745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26239585169320743151695163 39359377753981114727542745)
              ·
                refine ⟨29519533315485836045657059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39359377753981114727542745 29519533315485836045657059)
                ·
                  refine ⟨44279299973228754068485589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29519533315485836045657059 44279299973228754068485589)
                  ·
                    refine ⟨1037796093122548923480131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44279299973228754068485589 1037796093122548923480131)
                    ·
                      rfl

theorem cell22_3031651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_3031651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031651 prefixEnd_3031651 := by exact prefixLift 3031651
  have htrace : WordTrace (prefixWord ++ tailWord_3031651) baseStart_3031651 baseEnd_3031651 := by
    simpa [prefixWord, tailWord_3031651, baseEnd_3031651] using wordTrace_append hprefix tailTrace_3031651
  have hstable : (prefixWord ++ tailWord_3031651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031651).length < 2 ^ (prefixWord ++ tailWord_3031651).sum := by decide
  have hdescent : baseEnd_3031651 < baseStart_3031651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031670 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3031670 : Nat := 118140960795 + 3031670 * 2 ^ 59
def prefixEnd_3031670 : Nat := 4983230072969 + 3 ^ 40 * 3031670 * 2
def baseEnd_3031670 : Nat := 345934199070279735751691

theorem tailTrace_3031670 : CollatzResearch.WordTrace tailWord_3031670 prefixEnd_3031670 345934199070279735751691 := by
  unfold tailWord_3031670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910880557924052053718279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73716059284523221906328309 6910880557924052053718279)
  ·
    refine ⟨10366320836886078080577419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6910880557924052053718279 10366320836886078080577419)
    ·
      refine ⟨15549481255329117120866129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10366320836886078080577419 15549481255329117120866129)
      ·
        refine ⟨11662110941496837840649597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15549481255329117120866129 11662110941496837840649597)
        ·
          refine ⟨4373291603061314190243599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11662110941496837840649597 4373291603061314190243599)
          ·
            refine ⟨6559937404591971285365399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373291603061314190243599 6559937404591971285365399)
            ·
              refine ⟨9839906106887956928048099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559937404591971285365399 9839906106887956928048099)
              ·
                refine ⟨14759859160331935392072149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9839906106887956928048099 14759859160331935392072149)
                ·
                  refine ⟨345934199070279735751691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14759859160331935392072149 345934199070279735751691)
                  ·
                    rfl

theorem cell22_3031670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3031670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031670 prefixEnd_3031670 := by exact prefixLift 3031670
  have htrace : WordTrace (prefixWord ++ tailWord_3031670) baseStart_3031670 baseEnd_3031670 := by
    simpa [prefixWord, tailWord_3031670, baseEnd_3031670] using wordTrace_append hprefix tailTrace_3031670
  have hstable : (prefixWord ++ tailWord_3031670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031670).length < 2 ^ (prefixWord ++ tailWord_3031670).sum := by decide
  have hdescent : baseEnd_3031670 < baseStart_3031670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031730 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3031730 : Nat := 118140960795 + 3031730 * 2 ^ 59
def prefixEnd_3031730 : Nat := 4983230072969 + 3 ^ 40 * 3031730 * 2
def baseEnd_3031730 : Nat := 1037823136437019050754889

theorem tailTrace_3031730 : CollatzResearch.WordTrace tailWord_3031730 prefixEnd_3031730 1037823136437019050754889 := by
  unfold tailWord_3031730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644069326641865776669161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73717518204378308737784429 27644069326641865776669161)
  ·
    refine ⟨20733051994981399332501871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27644069326641865776669161 20733051994981399332501871)
    ·
      refine ⟨31099577992472098998752807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733051994981399332501871 31099577992472098998752807)
      ·
        refine ⟨46649366988708148498129211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099577992472098998752807 46649366988708148498129211)
        ·
          refine ⟨69974050483062222747193817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46649366988708148498129211 69974050483062222747193817)
          ·
            refine ⟨52480537862296667060395363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69974050483062222747193817 52480537862296667060395363)
            ·
              refine ⟨78720806793445000590593045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52480537862296667060395363 78720806793445000590593045)
              ·
                refine ⟨3690037818442734402684049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78720806793445000590593045 3690037818442734402684049)
                ·
                  refine ⟨2767528363832050802013037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690037818442734402684049 2767528363832050802013037)
                  ·
                    refine ⟨1037823136437019050754889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767528363832050802013037 1037823136437019050754889)
                    ·
                      rfl

theorem cell22_3031730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3031730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031730 prefixEnd_3031730 := by exact prefixLift 3031730
  have htrace : WordTrace (prefixWord ++ tailWord_3031730) baseStart_3031730 baseEnd_3031730 := by
    simpa [prefixWord, tailWord_3031730, baseEnd_3031730] using wordTrace_append hprefix tailTrace_3031730
  have hstable : (prefixWord ++ tailWord_3031730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031730).length < 2 ^ (prefixWord ++ tailWord_3031730).sum := by decide
  have hdescent : baseEnd_3031730 < baseStart_3031730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031743 : List Nat := [1, 1, 2, 2, 2, 5, 2, 7]
def baseStart_3031743 : Nat := 118140960795 + 3031743 * 2 ^ 59
def prefixEnd_3031743 : Nat := 4983230072969 + 3 ^ 40 * 3031743 * 2
def baseEnd_3031743 : Nat := 115314176289187927797761

theorem tailTrace_3031743 : CollatzResearch.WordTrace tailWord_3031743 prefixEnd_3031743 115314176289187927797761 := by
  unfold tailWord_3031743
  simp only [CollatzResearch.WordTrace]
  refine ⟨110576751455520366326899883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73717834303680244217933255 110576751455520366326899883)
  ·
    refine ⟨165865127183280549490349825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110576751455520366326899883 165865127183280549490349825)
    ·
      refine ⟨124398845387460412117762369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165865127183280549490349825 124398845387460412117762369)
      ·
        refine ⟨93299134040595309088321777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124398845387460412117762369 93299134040595309088321777)
        ·
          refine ⟨69974350530446481816241333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93299134040595309088321777 69974350530446481816241333)
          ·
            refine ⟨6560095362229357670272625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69974350530446481816241333 6560095362229357670272625)
            ·
              refine ⟨4920071521672018252704469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560095362229357670272625 4920071521672018252704469)
              ·
                refine ⟨115314176289187927797761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4920071521672018252704469 115314176289187927797761)
                ·
                  rfl

theorem cell22_3031743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 7].length) (baseStart_3031743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031743 prefixEnd_3031743 := by exact prefixLift 3031743
  have htrace : WordTrace (prefixWord ++ tailWord_3031743) baseStart_3031743 baseEnd_3031743 := by
    simpa [prefixWord, tailWord_3031743, baseEnd_3031743] using wordTrace_append hprefix tailTrace_3031743
  have hstable : (prefixWord ++ tailWord_3031743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031743).length < 2 ^ (prefixWord ++ tailWord_3031743).sum := by decide
  have hdescent : baseEnd_3031743 < baseStart_3031743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031762 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3031762 : Nat := 118140960795 + 3031762 * 2 ^ 59
def prefixEnd_3031762 : Nat := 4983230072969 + 3 ^ 40 * 3031762 * 2
def baseEnd_3031762 : Nat := 1037834090690981633954791

theorem tailTrace_3031762 : CollatzResearch.WordTrace tailWord_3031762 prefixEnd_3031762 1037834090690981633954791 := by
  unfold tailWord_3031762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644361110612883142960385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73718296294967688381227693 27644361110612883142960385)
  ·
    refine ⟨20733270832959662357220289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27644361110612883142960385 20733270832959662357220289)
    ·
      refine ⟨15549953124719746767915217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20733270832959662357220289 15549953124719746767915217)
      ·
        refine ⟨11662464843539810075936413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15549953124719746767915217 11662464843539810075936413)
        ·
          refine ⟨4373424316327428778476155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11662464843539810075936413 4373424316327428778476155)
          ·
            refine ⟨6560136474491143167714233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373424316327428778476155 6560136474491143167714233)
            ·
              refine ⟨4920102355868357375785675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560136474491143167714233 4920102355868357375785675)
              ·
                refine ⟨7380153533802536063678513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920102355868357375785675 7380153533802536063678513)
                ·
                  refine ⟨5535115150351902047758885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380153533802536063678513 5535115150351902047758885)
                  ·
                    refine ⟨1037834090690981633954791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535115150351902047758885 1037834090690981633954791)
                    ·
                      rfl

theorem cell22_3031762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3031762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031762 prefixEnd_3031762 := by exact prefixLift 3031762
  have htrace : WordTrace (prefixWord ++ tailWord_3031762) baseStart_3031762 baseEnd_3031762 := by
    simpa [prefixWord, tailWord_3031762, baseEnd_3031762] using wordTrace_append hprefix tailTrace_3031762
  have hstable : (prefixWord ++ tailWord_3031762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031762).length < 2 ^ (prefixWord ++ tailWord_3031762).sum := by decide
  have hdescent : baseEnd_3031762 < baseStart_3031762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031792 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_3031792 : Nat := 118140960795 + 3031792 * 2 ^ 59
def prefixEnd_3031792 : Nat := 4983230072969 + 3 ^ 40 * 3031792 * 2
def baseEnd_3031792 : Nat := 1037844360304071555704699

theorem tailTrace_3031792 : CollatzResearch.WordTrace tailWord_3031792 prefixEnd_3031792 1037844360304071555704699 := by
  unfold tailWord_3031792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55289269316171423847716815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73719025754895231796955753 55289269316171423847716815)
  ·
    refine ⟨82933903974257135771575223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55289269316171423847716815 82933903974257135771575223)
    ·
      refine ⟨124400855961385703657362835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82933903974257135771575223 124400855961385703657362835)
      ·
        refine ⟨186601283942078555486044253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124400855961385703657362835 186601283942078555486044253)
        ·
          refine ⟨69975481478279458307266595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186601283942078555486044253 69975481478279458307266595)
          ·
            refine ⟨104963222217419187460899893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69975481478279458307266595 104963222217419187460899893)
            ·
              refine ⟨9840302082883048824459365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104963222217419187460899893 9840302082883048824459365)
              ·
                refine ⟨1845056640540571654586131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9840302082883048824459365 1845056640540571654586131)
                ·
                  refine ⟨2767584960810857481879197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845056640540571654586131 2767584960810857481879197)
                  ·
                    refine ⟨1037844360304071555704699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767584960810857481879197 1037844360304071555704699)
                    ·
                      rfl

theorem cell22_3031792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_3031792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031792 prefixEnd_3031792 := by exact prefixLift 3031792
  have htrace : WordTrace (prefixWord ++ tailWord_3031792) baseStart_3031792 baseEnd_3031792 := by
    simpa [prefixWord, tailWord_3031792, baseEnd_3031792] using wordTrace_append hprefix tailTrace_3031792
  have hstable : (prefixWord ++ tailWord_3031792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031792).length < 2 ^ (prefixWord ++ tailWord_3031792).sum := by decide
  have hdescent : baseEnd_3031792 < baseStart_3031792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031863 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3031863 : Nat := 118140960795 + 3031863 * 2 ^ 59
def prefixEnd_3031863 : Nat := 4983230072969 + 3 ^ 40 * 3031863 * 2
def baseEnd_3031863 : Nat := 1037868665055051037179481

theorem tailTrace_3031863 : CollatzResearch.WordTrace tailWord_3031863 prefixEnd_3031863 1037868665055051037179481 := by
  unfold tailWord_3031863
  simp only [CollatzResearch.WordTrace]
  refine ⟨110581128215085626821268243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73720752143390417880845495 110581128215085626821268243)
  ·
    refine ⟨165871692322628440231902365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110581128215085626821268243 165871692322628440231902365)
    ·
      refine ⟨62201884620985665086963387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165871692322628440231902365 62201884620985665086963387)
      ·
        refine ⟨93302826931478497630445081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62201884620985665086963387 93302826931478497630445081)
        ·
          refine ⟨69977120198608873222833811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93302826931478497630445081 69977120198608873222833811)
          ·
            refine ⟨104965680297913309834250717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69977120198608873222833811 104965680297913309834250717)
            ·
              refine ⟨39362130111717491187844019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104965680297913309834250717 39362130111717491187844019)
              ·
                refine ⟨59043195167576236781766029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39362130111717491187844019 59043195167576236781766029)
                ·
                  refine ⟨22141198187841088793162261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59043195167576236781766029 22141198187841088793162261)
                  ·
                    refine ⟨1037868665055051037179481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22141198187841088793162261 1037868665055051037179481)
                    ·
                      rfl

theorem cell22_3031863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3031863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031863 prefixEnd_3031863 := by exact prefixLift 3031863
  have htrace : WordTrace (prefixWord ++ tailWord_3031863) baseStart_3031863 baseEnd_3031863 := by
    simpa [prefixWord, tailWord_3031863, baseEnd_3031863] using wordTrace_append hprefix tailTrace_3031863
  have hstable : (prefixWord ++ tailWord_3031863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031863).length < 2 ^ (prefixWord ++ tailWord_3031863).sum := by decide
  have hdescent : baseEnd_3031863 < baseStart_3031863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031869 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3031869 : Nat := 118140960795 + 3031869 * 2 ^ 59
def prefixEnd_3031869 : Nat := 4983230072969 + 3 ^ 40 * 3031869 * 2
def baseEnd_3031869 : Nat := 1037870718977669021529463

theorem tailTrace_3031869 : CollatzResearch.WordTrace tailWord_3031869 prefixEnd_3031869 1037870718977669021529463 := by
  unfold tailWord_3031869
  simp only [CollatzResearch.WordTrace]
  refine ⟨110581347053063889845986661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73720898035375926563991107 110581347053063889845986661)
  ·
    refine ⟨20734002572449479346122499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110581347053063889845986661 20734002572449479346122499)
    ·
      refine ⟨31101003858674219019183749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20734002572449479346122499 31101003858674219019183749)
      ·
        refine ⟨5831438223501416066096953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31101003858674219019183749 5831438223501416066096953)
        ·
          refine ⟨4373578667626062049572715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5831438223501416066096953 4373578667626062049572715)
          ·
            refine ⟨6560368001439093074359073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373578667626062049572715 6560368001439093074359073)
            ·
              refine ⟨4920276001079319805769305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560368001439093074359073 4920276001079319805769305)
              ·
                refine ⟨3690207000809489854326979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920276001079319805769305 3690207000809489854326979)
                ·
                  refine ⟨5535310501214234781490469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690207000809489854326979 5535310501214234781490469)
                  ·
                    refine ⟨1037870718977669021529463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535310501214234781490469 1037870718977669021529463)
                    ·
                      rfl

theorem cell22_3031869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3031869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031869 prefixEnd_3031869 := by exact prefixLift 3031869
  have htrace : WordTrace (prefixWord ++ tailWord_3031869) baseStart_3031869 baseEnd_3031869 := by
    simpa [prefixWord, tailWord_3031869, baseEnd_3031869] using wordTrace_append hprefix tailTrace_3031869
  have hstable : (prefixWord ++ tailWord_3031869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031869).length < 2 ^ (prefixWord ++ tailWord_3031869).sum := by decide
  have hdescent : baseEnd_3031869 < baseStart_3031869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031880 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3031880 : Nat := 118140960795 + 3031880 * 2 ^ 59
def prefixEnd_3031880 : Nat := 4983230072969 + 3 ^ 40 * 3031880 * 2
def baseEnd_3031880 : Nat := 1037874484502468659504429

theorem tailTrace_3031880 : CollatzResearch.WordTrace tailWord_3031880 prefixEnd_3031880 1037874484502468659504429 := by
  unfold tailWord_3031880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55290874128012019362318547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73721165504016025816424729 55290874128012019362318547)
  ·
    refine ⟨82936311192018029043477821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55290874128012019362318547 82936311192018029043477821)
    ·
      refine ⟨31101116697006760891304183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82936311192018029043477821 31101116697006760891304183)
      ·
        refine ⟨46651675045510141336956275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31101116697006760891304183 46651675045510141336956275)
        ·
          refine ⟨69977512568265212005434413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46651675045510141336956275 69977512568265212005434413)
          ·
            refine ⟨26241567213099454502037905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69977512568265212005434413 26241567213099454502037905)
            ·
              refine ⟨19681175409824590876528429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26241567213099454502037905 19681175409824590876528429)
              ·
                refine ⟨7380440778684221578698161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19681175409824590876528429 7380440778684221578698161)
                ·
                  refine ⟨5535330584013166184023621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380440778684221578698161 5535330584013166184023621)
                  ·
                    refine ⟨1037874484502468659504429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535330584013166184023621 1037874484502468659504429)
                    ·
                      rfl

theorem cell22_3031880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3031880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031880 prefixEnd_3031880 := by exact prefixLift 3031880
  have htrace : WordTrace (prefixWord ++ tailWord_3031880) baseStart_3031880 baseEnd_3031880 := by
    simpa [prefixWord, tailWord_3031880, baseEnd_3031880] using wordTrace_append hprefix tailTrace_3031880
  have hstable : (prefixWord ++ tailWord_3031880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031880).length < 2 ^ (prefixWord ++ tailWord_3031880).sum := by decide
  have hdescent : baseEnd_3031880 < baseStart_3031880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031884 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_3031884 : Nat := 118140960795 + 3031884 * 2 ^ 59
def prefixEnd_3031884 : Nat := 4983230072969 + 3 ^ 40 * 3031884 * 2
def baseEnd_3031884 : Nat := 345958617928071327468139

theorem tailTrace_3031884 : CollatzResearch.WordTrace tailWord_3031884 prefixEnd_3031884 345958617928071327468139 := by
  unfold tailWord_3031884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55290947074004773703891353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73721262765339698271855137 55290947074004773703891353)
  ·
    refine ⟨41468210305503580277918515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55290947074004773703891353 41468210305503580277918515)
    ·
      refine ⟨62202315458255370416877773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41468210305503580277918515 62202315458255370416877773)
      ·
        refine ⟨23325868296845763906329165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62202315458255370416877773 23325868296845763906329165)
        ·
          refine ⟨8747200611317161464873437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23325868296845763906329165 8747200611317161464873437)
          ·
            refine ⟨3280200229243935549327539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8747200611317161464873437 3280200229243935549327539)
            ·
              refine ⟨4920300343865903323991309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280200229243935549327539 4920300343865903323991309)
              ·
                refine ⟨1845112628949713746496741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920300343865903323991309 1845112628949713746496741)
                ·
                  refine ⟨345958617928071327468139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845112628949713746496741 345958617928071327468139)
                  ·
                    rfl

theorem cell22_3031884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_3031884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031884 prefixEnd_3031884 := by exact prefixLift 3031884
  have htrace : WordTrace (prefixWord ++ tailWord_3031884) baseStart_3031884 baseEnd_3031884 := by
    simpa [prefixWord, tailWord_3031884, baseEnd_3031884] using wordTrace_append hprefix tailTrace_3031884
  have hstable : (prefixWord ++ tailWord_3031884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031884).length < 2 ^ (prefixWord ++ tailWord_3031884).sum := by decide
  have hdescent : baseEnd_3031884 < baseStart_3031884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031895 : List Nat := [1, 1, 3, 2, 4, 3, 8]
def baseStart_3031895 : Nat := 118140960795 + 3031895 * 2 ^ 59
def prefixEnd_3031895 : Nat := 4983230072969 + 3 ^ 40 * 3031895 * 2
def baseEnd_3031895 : Nat := 38439985900333837791829

theorem tailTrace_3031895 : CollatzResearch.WordTrace tailWord_3031895 prefixEnd_3031895 38439985900333837791829 := by
  unfold tailWord_3031895
  simp only [CollatzResearch.WordTrace]
  refine ⟨110582295350969696286433139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73721530233979797524288759 110582295350969696286433139)
  ·
    refine ⟨165873443026454544429649709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110582295350969696286433139 165873443026454544429649709)
    ·
      refine ⟨62202541134920454161118641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165873443026454544429649709 62202541134920454161118641)
      ·
        refine ⟨46651905851190340620838981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62202541134920454161118641 46651905851190340620838981)
        ·
          refine ⟨8747232347098188866407309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46651905851190340620838981 8747232347098188866407309)
          ·
            refine ⟨3280212130161820824902741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8747232347098188866407309 3280212130161820824902741)
            ·
              refine ⟨38439985900333837791829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3280212130161820824902741 38439985900333837791829)
              ·
                rfl

theorem cell22_3031895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 8].length) (baseStart_3031895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031895 prefixEnd_3031895 := by exact prefixLift 3031895
  have htrace : WordTrace (prefixWord ++ tailWord_3031895) baseStart_3031895 baseEnd_3031895 := by
    simpa [prefixWord, tailWord_3031895, baseEnd_3031895] using wordTrace_append hprefix tailTrace_3031895
  have hstable : (prefixWord ++ tailWord_3031895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031895).length < 2 ^ (prefixWord ++ tailWord_3031895).sum := by decide
  have hdescent : baseEnd_3031895 < baseStart_3031895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031957 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 5]
def baseStart_3031957 : Nat := 118140960795 + 3031957 * 2 ^ 59
def prefixEnd_3031957 : Nat := 4983230072969 + 3 ^ 40 * 3031957 * 2
def baseEnd_3031957 : Nat := 345966947725355375109731

theorem tailTrace_3031957 : CollatzResearch.WordTrace tailWord_3031957 prefixEnd_3031957 345966947725355375109731 := by
  unfold tailWord_3031957
  simp only [CollatzResearch.WordTrace]
  refine ⟨110584556676745080875190125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73723037784496720583460083 110584556676745080875190125)
  ·
    refine ⟨41469208753779405328196297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110584556676745080875190125 41469208753779405328196297)
    ·
      refine ⟨31101906565334553996147223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41469208753779405328196297 31101906565334553996147223)
      ·
        refine ⟨46652859848001830994220835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31101906565334553996147223 46652859848001830994220835)
        ·
          refine ⟨69979289772002746491331253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46652859848001830994220835 69979289772002746491331253)
          ·
            refine ⟨6560558416125257483562305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69979289772002746491331253 6560558416125257483562305)
            ·
              refine ⟨4920418812093943112671729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560558416125257483562305 4920418812093943112671729)
              ·
                refine ⟨3690314109070457334503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920418812093943112671729 3690314109070457334503797)
                ·
                  refine ⟨345966947725355375109731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690314109070457334503797 345966947725355375109731)
                  ·
                    rfl

theorem cell22_3031957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_3031957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3031957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3031957 prefixEnd_3031957 := by exact prefixLift 3031957
  have htrace : WordTrace (prefixWord ++ tailWord_3031957) baseStart_3031957 baseEnd_3031957 := by
    simpa [prefixWord, tailWord_3031957, baseEnd_3031957] using wordTrace_append hprefix tailTrace_3031957
  have hstable : (prefixWord ++ tailWord_3031957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031957).length < 2 ^ (prefixWord ++ tailWord_3031957).sum := by decide
  have hdescent : baseEnd_3031957 < baseStart_3031957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032017 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_3032017 : Nat := 118140960795 + 3032017 * 2 ^ 59
def prefixEnd_3032017 : Nat := 4983230072969 + 3 ^ 40 * 3032017 * 2
def baseEnd_3032017 : Nat := 1037921382402245968829009

theorem tailTrace_3032017 : CollatzResearch.WordTrace tailWord_3032017 prefixEnd_3032017 1037921382402245968829009 := by
  unfold tailWord_3032017
  simp only [CollatzResearch.WordTrace]
  refine ⟨110586745056527711122374305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73724496704351807414916203 110586745056527711122374305)
  ·
    refine ⟨82940058792395783341780729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110586745056527711122374305 82940058792395783341780729)
    ·
      refine ⟨62205044094296837506335547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82940058792395783341780729 62205044094296837506335547)
      ·
        refine ⟨93307566141445256259503321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62205044094296837506335547 93307566141445256259503321)
        ·
          refine ⟨69980674606083942194627491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93307566141445256259503321 69980674606083942194627491)
          ·
            refine ⟨104971011909125913291941237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69980674606083942194627491 104971011909125913291941237)
            ·
              refine ⟨9841032366480554371119491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104971011909125913291941237 9841032366480554371119491)
              ·
                refine ⟨14761548549720831556679237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9841032366480554371119491 14761548549720831556679237)
                ·
                  refine ⟨2767790353072655916877357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14761548549720831556679237 2767790353072655916877357)
                  ·
                    refine ⟨1037921382402245968829009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2767790353072655916877357 1037921382402245968829009)
                    ·
                      rfl

theorem cell22_3032017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_3032017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032017 prefixEnd_3032017 := by exact prefixLift 3032017
  have htrace : WordTrace (prefixWord ++ tailWord_3032017) baseStart_3032017 baseEnd_3032017 := by
    simpa [prefixWord, tailWord_3032017, baseEnd_3032017] using wordTrace_append hprefix tailTrace_3032017
  have hstable : (prefixWord ++ tailWord_3032017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032017).length < 2 ^ (prefixWord ++ tailWord_3032017).sum := by decide
  have hdescent : baseEnd_3032017 < baseStart_3032017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032047 : List Nat := [1, 1, 2, 1, 4, 3, 4, 6]
def baseStart_3032047 : Nat := 118140960795 + 3032047 * 2 ^ 59
def prefixEnd_3032047 : Nat := 4983230072969 + 3 ^ 40 * 3032047 * 2
def baseEnd_3032047 : Nat := 115325739112815098953213

theorem tailTrace_3032047 : CollatzResearch.WordTrace tailWord_3032047 prefixEnd_3032047 115325739112815098953213 := by
  unfold tailWord_3032047
  simp only [CollatzResearch.WordTrace]
  refine ⟨110587839246419026245966395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73725226164279350830644263 110587839246419026245966395)
  ·
    refine ⟨165881758869628539368949593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110587839246419026245966395 165881758869628539368949593)
    ·
      refine ⟨124411319152221404526712195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165881758869628539368949593 124411319152221404526712195)
      ·
        refine ⟨186616978728332106790068293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124411319152221404526712195 186616978728332106790068293)
        ·
          refine ⟨34990683511562270023137805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186616978728332106790068293 34990683511562270023137805)
          ·
            refine ⟨13121506316835851258676677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34990683511562270023137805 13121506316835851258676677)
            ·
              refine ⟨2460282434406722111001877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13121506316835851258676677 2460282434406722111001877)
              ·
                refine ⟨115325739112815098953213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2460282434406722111001877 115325739112815098953213)
                ·
                  rfl

theorem cell22_3032047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 6].length) (baseStart_3032047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032047 prefixEnd_3032047 := by exact prefixLift 3032047
  have htrace : WordTrace (prefixWord ++ tailWord_3032047) baseStart_3032047 baseEnd_3032047 := by
    simpa [prefixWord, tailWord_3032047, baseEnd_3032047] using wordTrace_append hprefix tailTrace_3032047
  have hstable : (prefixWord ++ tailWord_3032047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032047).length < 2 ^ (prefixWord ++ tailWord_3032047).sum := by decide
  have hdescent : baseEnd_3032047 < baseStart_3032047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032126 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3032126 : Nat := 118140960795 + 3032126 * 2 ^ 59
def prefixEnd_3032126 : Nat := 4983230072969 + 3 ^ 40 * 3032126 * 2
def baseEnd_3032126 : Nat := 345986231776602005951225

theorem tailTrace_3032126 : CollatzResearch.WordTrace tailWord_3032126 prefixEnd_3032126 345986231776602005951225 := by
  unfold tailWord_3032126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823840076641602842261529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73727147075421881825394821 13823840076641602842261529)
  ·
    refine ⟨10367880057481202131696147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13823840076641602842261529 10367880057481202131696147)
    ·
      refine ⟨15551820086221803197544221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10367880057481202131696147 15551820086221803197544221)
      ·
        refine ⟨5831932532333176199079083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15551820086221803197544221 5831932532333176199079083)
        ·
          refine ⟨8747898798499764298618625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831932532333176199079083 8747898798499764298618625)
          ·
            refine ⟨6560924098874823223963969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8747898798499764298618625 6560924098874823223963969)
            ·
              refine ⟨4920693074156117417972977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560924098874823223963969 4920693074156117417972977)
              ·
                refine ⟨3690519805617088063479733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920693074156117417972977 3690519805617088063479733)
                ·
                  refine ⟨345986231776602005951225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690519805617088063479733 345986231776602005951225)
                  ·
                    rfl

theorem cell22_3032126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3032126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032126 prefixEnd_3032126 := by exact prefixLift 3032126
  have htrace : WordTrace (prefixWord ++ tailWord_3032126) baseStart_3032126 baseEnd_3032126 := by
    simpa [prefixWord, tailWord_3032126, baseEnd_3032126] using wordTrace_append hprefix tailTrace_3032126
  have hstable : (prefixWord ++ tailWord_3032126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032126).length < 2 ^ (prefixWord ++ tailWord_3032126).sum := by decide
  have hdescent : baseEnd_3032126 < baseStart_3032126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032173 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3032173 : Nat := 118140960795 + 3032173 * 2 ^ 59
def prefixEnd_3032173 : Nat := 4983230072969 + 3 ^ 40 * 3032173 * 2
def baseEnd_3032173 : Nat := 1037974784390313561928531

theorem tailTrace_3032173 : CollatzResearch.WordTrace tailWord_3032173 prefixEnd_3032173 1037974784390313561928531 := by
  unfold tailWord_3032173
  simp only [CollatzResearch.WordTrace]
  refine ⟨110592434843962549765053173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73728289895975033176702115 110592434843962549765053173)
  ·
    refine ⟨10368040766621489040473735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110592434843962549765053173 10368040766621489040473735)
    ·
      refine ⟨15552061149932233560710603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368040766621489040473735 15552061149932233560710603)
      ·
        refine ⟨23328091724898350341065905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15552061149932233560710603 23328091724898350341065905)
        ·
          refine ⟨17496068793673762755799429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23328091724898350341065905 17496068793673762755799429)
          ·
            refine ⟨3280512898813830516712393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17496068793673762755799429 3280512898813830516712393)
            ·
              refine ⟨2460384674110372887534295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280512898813830516712393 2460384674110372887534295)
              ·
                refine ⟨3690577011165559331301443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460384674110372887534295 3690577011165559331301443)
                ·
                  refine ⟨5535865516748338996952165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690577011165559331301443 5535865516748338996952165)
                  ·
                    refine ⟨1037974784390313561928531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535865516748338996952165 1037974784390313561928531)
                    ·
                      rfl

theorem cell22_3032173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3032173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032173 prefixEnd_3032173 := by exact prefixLift 3032173
  have htrace : WordTrace (prefixWord ++ tailWord_3032173) baseStart_3032173 baseEnd_3032173 := by
    simpa [prefixWord, tailWord_3032173, baseEnd_3032173] using wordTrace_append hprefix tailTrace_3032173
  have hstable : (prefixWord ++ tailWord_3032173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032173).length < 2 ^ (prefixWord ++ tailWord_3032173).sum := by decide
  have hdescent : baseEnd_3032173 < baseStart_3032173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032216 : List Nat := [2, 1, 2, 4, 2, 3, 2, 6]
def baseStart_3032216 : Nat := 118140960795 + 3032216 * 2 ^ 59
def prefixEnd_3032216 : Nat := 4983230072969 + 3 ^ 40 * 3032216 * 2
def baseEnd_3032216 : Nat := 115332167129897309233711

theorem tailTrace_3032216 : CollatzResearch.WordTrace tailWord_3032216 prefixEnd_3032216 115332167129897309233711 := by
  unfold tailWord_3032216
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297001591403384054434251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73729335455204512072579001 55297001591403384054434251)
  ·
    refine ⟨82945502387105076081651377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55297001591403384054434251 82945502387105076081651377)
    ·
      refine ⟨62209126790328807061238533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82945502387105076081651377 62209126790328807061238533)
      ·
        refine ⟨11664211273186651323982225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62209126790328807061238533 11664211273186651323982225)
        ·
          refine ⟨8748158454889988492986669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11664211273186651323982225 8748158454889988492986669)
          ·
            refine ⟨3280559420583745684870001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8748158454889988492986669 3280559420583745684870001)
            ·
              refine ⟨2460419565437809263652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280559420583745684870001 2460419565437809263652501)
              ·
                refine ⟨115332167129897309233711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2460419565437809263652501 115332167129897309233711)
                ·
                  rfl

theorem cell22_3032216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_3032216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032216 prefixEnd_3032216 := by exact prefixLift 3032216
  have htrace : WordTrace (prefixWord ++ tailWord_3032216) baseStart_3032216 baseEnd_3032216 := by
    simpa [prefixWord, tailWord_3032216, baseEnd_3032216] using wordTrace_append hprefix tailTrace_3032216
  have hstable : (prefixWord ++ tailWord_3032216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032216).length < 2 ^ (prefixWord ++ tailWord_3032216).sum := by decide
  have hdescent : baseEnd_3032216 < baseStart_3032216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032321 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3032321 : Nat := 118140960795 + 3032321 * 2 ^ 59
def prefixEnd_3032321 : Nat := 4983230072969 + 3 ^ 40 * 3032321 * 2
def baseEnd_3032321 : Nat := 1038025447814890509228077

theorem tailTrace_3032321 : CollatzResearch.WordTrace tailWord_3032321 prefixEnd_3032321 1038025447814890509228077 := by
  unfold tailWord_3032321
  simp only [CollatzResearch.WordTrace]
  refine ⟨110597832847426371041440817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73731888564950914027627211 110597832847426371041440817)
  ·
    refine ⟨82948374635569778281080613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110597832847426371041440817 82948374635569778281080613)
    ·
      refine ⟨15552820244169333427702615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82948374635569778281080613 15552820244169333427702615)
      ·
        refine ⟨23329230366254000141553923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15552820244169333427702615 23329230366254000141553923)
        ·
          refine ⟨34993845549381000212330885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23329230366254000141553923 34993845549381000212330885)
          ·
            refine ⟨6561346040508937539812041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34993845549381000212330885 6561346040508937539812041)
            ·
              refine ⟨4921009530381703154859031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561346040508937539812041 4921009530381703154859031)
              ·
                refine ⟨7381514295572554732288547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921009530381703154859031 7381514295572554732288547)
                ·
                  refine ⟨11072271443358832098432821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381514295572554732288547 11072271443358832098432821)
                  ·
                    refine ⟨1038025447814890509228077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11072271443358832098432821 1038025447814890509228077)
                    ·
                      rfl

theorem cell22_3032321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3032321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032321 prefixEnd_3032321 := by exact prefixLift 3032321
  have htrace : WordTrace (prefixWord ++ tailWord_3032321) baseStart_3032321 baseEnd_3032321 := by
    simpa [prefixWord, tailWord_3032321, baseEnd_3032321] using wordTrace_append hprefix tailTrace_3032321
  have hstable : (prefixWord ++ tailWord_3032321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032321).length < 2 ^ (prefixWord ++ tailWord_3032321).sum := by decide
  have hdescent : baseEnd_3032321 < baseStart_3032321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032394 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3032394 : Nat := 118140960795 + 3032394 * 2 ^ 59
def prefixEnd_3032394 : Nat := 4983230072969 + 3 ^ 40 * 3032394 * 2
def baseEnd_3032394 : Nat := 1038050437206742652152853

theorem tailTrace_3032394 : CollatzResearch.WordTrace tailWord_3032394 prefixEnd_3032394 1038050437206742652152853 := by
  unfold tailWord_3032394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27650123844040476127212059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73733663584107936339232157 27650123844040476127212059)
  ·
    refine ⟨41475185766060714190818089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27650123844040476127212059 41475185766060714190818089)
    ·
      refine ⟨31106389324545535643113567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41475185766060714190818089 31106389324545535643113567)
      ·
        refine ⟨46659583986818303464670351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31106389324545535643113567 46659583986818303464670351)
        ·
          refine ⟨69989375980227455197005527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46659583986818303464670351 69989375980227455197005527)
          ·
            refine ⟨104984063970341182795508291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69989375980227455197005527 104984063970341182795508291)
            ·
              refine ⟨157476095955511774193262437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104984063970341182795508291 157476095955511774193262437)
              ·
                refine ⟨29526767991658457661236707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157476095955511774193262437 29526767991658457661236707)
                ·
                  refine ⟨44290151987487686491855061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29526767991658457661236707 44290151987487686491855061)
                  ·
                    refine ⟨1038050437206742652152853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44290151987487686491855061 1038050437206742652152853)
                    ·
                      rfl

theorem cell22_3032394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3032394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032394 prefixEnd_3032394 := by exact prefixLift 3032394
  have htrace : WordTrace (prefixWord ++ tailWord_3032394) baseStart_3032394 baseEnd_3032394 := by
    simpa [prefixWord, tailWord_3032394, baseEnd_3032394] using wordTrace_append hprefix tailTrace_3032394
  have hstable : (prefixWord ++ tailWord_3032394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032394).length < 2 ^ (prefixWord ++ tailWord_3032394).sum := by decide
  have hdescent : baseEnd_3032394 < baseStart_3032394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032430 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_3032430 : Nat := 118140960795 + 3032430 * 2 ^ 59
def prefixEnd_3032430 : Nat := 4983230072969 + 3 ^ 40 * 3032430 * 2
def baseEnd_3032430 : Nat := 346020920247483519417581

theorem tailTrace_3032430 : CollatzResearch.WordTrace tailWord_3032430 prefixEnd_3032430 346020920247483519417581 := by
  unfold tailWord_3032430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825226050503935332144843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73734538936020988438105829 13825226050503935332144843)
  ·
    refine ⟨20737839075755902998217265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13825226050503935332144843 20737839075755902998217265)
    ·
      refine ⟨15553379306816927248662949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20737839075755902998217265 15553379306816927248662949)
      ·
        refine ⟨2916258620028173859124303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15553379306816927248662949 2916258620028173859124303)
        ·
          refine ⟨4374387930042260788686455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916258620028173859124303 4374387930042260788686455)
          ·
            refine ⟨6561581895063391183029683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374387930042260788686455 6561581895063391183029683)
            ·
              refine ⟨9842372842595086774544525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561581895063391183029683 9842372842595086774544525)
              ·
                refine ⟨3690889815973157540454197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9842372842595086774544525 3690889815973157540454197)
                ·
                  refine ⟨346020920247483519417581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690889815973157540454197 346020920247483519417581)
                  ·
                    rfl

theorem cell22_3032430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_3032430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032430 prefixEnd_3032430 := by exact prefixLift 3032430
  have htrace : WordTrace (prefixWord ++ tailWord_3032430) baseStart_3032430 baseEnd_3032430 := by
    simpa [prefixWord, tailWord_3032430, baseEnd_3032430] using wordTrace_append hprefix tailTrace_3032430
  have hstable : (prefixWord ++ tailWord_3032430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032430).length < 2 ^ (prefixWord ++ tailWord_3032430).sum := by decide
  have hdescent : baseEnd_3032430 < baseStart_3032430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032456 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3032456 : Nat := 118140960795 + 3032456 * 2 ^ 59
def prefixEnd_3032456 : Nat := 4983230072969 + 3 ^ 40 * 3032456 * 2
def baseEnd_3032456 : Nat := 1038071661073795157102663

theorem tailTrace_3032456 : CollatzResearch.WordTrace tailWord_3032456 prefixEnd_3032456 1038071661073795157102663 := by
  unfold tailWord_3032456
  simp only [CollatzResearch.WordTrace]
  refine ⟨55301378350968644548802611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73735171134624859398403481 55301378350968644548802611)
  ·
    refine ⟨82952067526452966823203917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55301378350968644548802611 82952067526452966823203917)
    ·
      refine ⟨31107025322419862558701469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82952067526452966823203917 31107025322419862558701469)
      ·
        refine ⟨11665134495907448459513051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31107025322419862558701469 11665134495907448459513051)
        ·
          refine ⟨17497701743861172689269577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11665134495907448459513051 17497701743861172689269577)
          ·
            refine ⟨13123276307895879516952183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17497701743861172689269577 13123276307895879516952183)
            ·
              refine ⟨19684914461843819275428275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13123276307895879516952183 19684914461843819275428275)
              ·
                refine ⟨29527371692765728913142413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19684914461843819275428275 29527371692765728913142413)
                ·
                  refine ⟨11072764384787148342428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29527371692765728913142413 11072764384787148342428405)
                  ·
                    refine ⟨1038071661073795157102663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11072764384787148342428405 1038071661073795157102663)
                    ·
                      rfl

theorem cell22_3032456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3032456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032456 prefixEnd_3032456 := by exact prefixLift 3032456
  have htrace : WordTrace (prefixWord ++ tailWord_3032456) baseStart_3032456 baseEnd_3032456 := by
    simpa [prefixWord, tailWord_3032456, baseEnd_3032456] using wordTrace_append hprefix tailTrace_3032456
  have hstable : (prefixWord ++ tailWord_3032456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032456).length < 2 ^ (prefixWord ++ tailWord_3032456).sum := by decide
  have hdescent : baseEnd_3032456 < baseStart_3032456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032473 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_3032473 : Nat := 118140960795 + 3032473 * 2 ^ 59
def prefixEnd_3032473 : Nat := 4983230072969 + 3 ^ 40 * 3032473 * 2
def baseEnd_3032473 : Nat := 1038077480521212779427611

theorem tailTrace_3032473 : CollatzResearch.WordTrace tailWord_3032473 prefixEnd_3032473 1038077480521212779427611 := by
  unfold tailWord_3032473
  simp only [CollatzResearch.WordTrace]
  refine ⟨110603376742875701000974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73735584495250467333982715 110603376742875701000974073)
  ·
    refine ⟨82952532557156775750730555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110603376742875701000974073 82952532557156775750730555)
    ·
      refine ⟨124428798835735163626095833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82952532557156775750730555 124428798835735163626095833)
      ·
        refine ⟨93321599126801372719571875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124428798835735163626095833 93321599126801372719571875)
        ·
          refine ⟨139982398690202059079357813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93321599126801372719571875 139982398690202059079357813)
          ·
            refine ⟨13123349877206443038689795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139982398690202059079357813 13123349877206443038689795)
            ·
              refine ⟨19685024815809664558034693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13123349877206443038689795 19685024815809664558034693)
              ·
                refine ⟨3690942152964312104631505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19685024815809664558034693 3690942152964312104631505)
                ·
                  refine ⟨2768206614723234078473629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690942152964312104631505 2768206614723234078473629)
                  ·
                    refine ⟨1038077480521212779427611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768206614723234078473629 1038077480521212779427611)
                    ·
                      rfl

theorem cell22_3032473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_3032473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032473 prefixEnd_3032473 := by exact prefixLift 3032473
  have htrace : WordTrace (prefixWord ++ tailWord_3032473) baseStart_3032473 baseEnd_3032473 := by
    simpa [prefixWord, tailWord_3032473, baseEnd_3032473] using wordTrace_append hprefix tailTrace_3032473
  have hstable : (prefixWord ++ tailWord_3032473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032473).length < 2 ^ (prefixWord ++ tailWord_3032473).sum := by decide
  have hdescent : baseEnd_3032473 < baseStart_3032473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
